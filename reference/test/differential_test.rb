# frozen_string_literal: true

require_relative "test_helper"
require_relative "model_generator"
require_relative "composite_generator"
require "open3"
require "tmpdir"

# 参照実装と `fmspec` コマンドの結果を突き合わせる（仕様書 §14.3）。
# 探索器、IRの読み込み、結果の直列化は証明の対象外なので、ここで検査する。
#
#   FMSPEC_BIN   比較する実行ファイル（既定は target/debug/fmspec）
#   FMSPEC_FUZZ  ランダム生成するモデルの数（既定は300。複合型のモデルも同じ数）
#   FMSPEC_SEED  生成の種（既定は1）
class DifferentialTest < Minitest::Test
  BIN = ENV.fetch("FMSPEC_BIN", File.join(ROOT, "target/debug/fmspec"))
  COUNT = Integer(ENV.fetch("FMSPEC_FUZZ", "300"))
  SEED = Integer(ENV.fetch("FMSPEC_SEED", "1"))

  def setup
    skip "#{BIN} がありません。先に cargo build を実行してください" unless File.executable?(BIN)
    @dir = Dir.mktmpdir("fmspec")
  end

  def teardown
    FileUtils.remove_entry(@dir) if @dir
  end

  def cli(*args)
    out, status = Open3.capture2(BIN, *args, "--json")
    [JSON.parse(out.force_encoding(Encoding::UTF_8)), status.exitstatus]
  end

  def flags(deadlock: false, max_states: nil, max_depth: nil, actions: nil)
    list = []
    list << "--deadlock" if deadlock
    list += ["--max-states", max_states.to_s] if max_states
    list += ["--max-depth", max_depth.to_s] if max_depth
    list += ["--actions", actions.join(",")] if actions
    list
  end

  EXIT = { "verified" => 0, "violated" => 1, "error" => 2, "inconclusive" => 3 }.freeze

  # 同じモデルと検査条件で両方を実行し、結果を比べる。エンジンの結果を返す。
  def compare(ir, label, **options)
    path = File.join(@dir, "model.json")
    cert = File.join(@dir, "certificate.json")
    File.write(path, JSON.generate(ir))
    File.delete(cert) if File.exist?(cert)
    expected = reference(ir).check(**options)
    actual, code = cli("check", path, "--certificate-out", cert, *flags(**options))
    context = -> { "#{label}\n#{JSON.generate(ir)}\noptions: #{options}\nreference: #{expected}\nengine: #{actual}" }

    assert_equal expected["status"], actual["status"], context
    assert_equal EXIT.fetch(expected["status"]), code, context
    assert_equal expected["visited_states"], actual["search"]["visited_states"], context
    case expected["status"]
    when "verified"
      assert_equal expected["certificate"], JSON.parse(File.read(cert, encoding: Encoding::UTF_8))["states"], context
    when "violated", "error"
      assert_equal expected["property"], actual["property"].except("source"), context
      assert_equal expected["initial"], actual["trace"]["initial"], context
      assert_equal expected["steps"], actual["trace"]["steps"], context
    else
      assert_equal expected["reason"], actual["reason"], context
    end
    [expected, path, cert]
  end

  def test_fixed_models
    models = {
      "tickets" => Models.tickets,
      "tickets_without_guard" => Models.tickets_without_guard,
      "responder" => Models.responder,
      "stuck" => Models.counter(0, []),
      "loop" => Models.counter(1, [Models.stay, Models.go("go", 0, 1)]),
      "overflow" => Models.big({ "all" => [{ "bool" => true }, Models.overflowing] })
    }
    models.each do |name, ir|
      [false, true].each do |deadlock|
        [nil, 1, 2].each { |max| compare(ir, name, deadlock: deadlock, max_states: max) }
        [0, 1, 2].each { |max| compare(ir, name, deadlock: deadlock, max_depth: max) }
      end
    end
  end

  def test_random_models
    statuses = Hash.new(0)
    COUNT.times do |n|
      seed = SEED * 1_000_003 + n
      rng = Random.new(seed)
      ir = ModelGenerator.new(seed).model
      options = { deadlock: rng.rand < 0.5 }
      options[:max_states] = rng.rand(1..6) if rng.rand < 0.2
      names = ir["actions"].map { |a| a["name"] }
      options[:actions] = names.select { rng.rand < 0.7 } if rng.rand < 0.2
      with_depth(options, seed)
      expected, path, cert = compare(ir, "seed #{seed}", **options)
      statuses[expected["status"]] += 1
      compare_certificates(ir, expected, path, cert, rng, options) if expected["status"] == "verified"
      compare_simulation(ir, path, rng, options.except(:max_states, :max_depth))
    end
    # 生成器が片寄って、どれかの結果をまったく試していない、ということがないようにする。
    %w[verified violated error].each { |s| assert_operator statuses[s], :>, COUNT / 30, "結果の分布: #{statuses}" }
  end

  # 評価の順序、検査の順序、範囲外更新の位置を決める境界の式。ランダムな生成では当たりにくいものを並べる。
  def test_fixed_composite_models
    int = ->(n) { { "int" => n } }
    small = { "int" => { "min" => 0, "max" => 1 } }
    boom = { "unwrap" => [{ "none" => small }] }
    zero_div = { "eq" => [{ "div" => [int.(1), int.(0)] }, int.(0)] }
    list = ->(*xs) { { "list" => { "of" => small, "max" => 1, "items" => xs.map(&int) } } }
    set = ->(*xs) { { "set" => { "of" => small, "items" => xs.map(&int) } } }
    map = { "map" => { "key" => small, "value" => small, "items" => [[int.(1), int.(0)], [int.(0), int.(1)]] } }
    opt = { "option" => { "bool" => {} } }
    picky = ->(x, bad, good) { { "ite" => [{ "eq" => [x, bad] }, zero_div, { "ne" => [x, good] }] } }
    exprs = {
      "put_key_first" => { "is_empty" => [{ "put" => [map, int.(5), boom] }] },
      "push_domain_first" => { "is_empty" => [{ "push" => [list.(0), int.(5)] }] },
      "set_items_in_order" => { "is_empty" => [set.(0, 5, 1 + 2**62)] },
      "forall_set_order" => { "forall" => { "name" => "x", "in" => set.(1, 0), "body" => picky.({ "local" => "x" }, int.(1), int.(0)) } },
      "forall_keys_order" => { "forall" => { "name" => "x", "in" => map, "body" => picky.({ "local" => "x" }, int.(1), int.(0)) } },
      "exists_type_order" => { "exists" => { "name" => "x", "type" => opt,
                                             "body" => { "ite" => [{ "is_none" => [{ "local" => "x" }] }, { "bool" => true }, zero_div] } } },
      "forall_list_order" => { "forall" => { "name" => "x", "in" => { "list" => { "of" => small, "max" => 2, "items" => [int.(1), int.(0)] } },
                                             "body" => picky.({ "local" => "x" }, int.(0), int.(1)) } },
      # 量化は本体の失敗を保留する。後ろで値が決まればその値、決まらなければ最初の失敗になる。
      "forall_error_then_false" => { "forall" => { "name" => "x", "type" => small,
                                                   "body" => { "ite" => [{ "eq" => [{ "local" => "x" }, int.(0)] }, zero_div, { "bool" => false }] } } },
      "forall_error_then_true" => { "forall" => { "name" => "x", "type" => small,
                                                  "body" => { "ite" => [{ "eq" => [{ "local" => "x" }, int.(0)] }, zero_div, { "bool" => true }] } } },
      "exists_error_then_true" => { "exists" => { "name" => "x", "type" => { "bool" => {} },
                                                  "body" => { "ite" => [{ "local" => "x" }, { "bool" => true }, zero_div] } } },
      "forall_first_error" => { "forall" => { "name" => "x", "type" => small,
                                              "body" => { "ite" => [{ "eq" => [{ "local" => "x" }, int.(0)] }, zero_div, { "eq" => [boom, int.(0)] }] } } },
      "forall_set_error_then_false" => { "forall" => { "name" => "x", "in" => set.(1, 0), "body" => picky.({ "local" => "x" }, int.(0), int.(1)) } },
      "eq_evaluates_both" => { "eq" => [{ "tuple" => [int.(1), boom] }, { "tuple" => [int.(0), int.(0)] }] },
      "let_is_eager" => { "let" => { "name" => "y", "value" => boom, "body" => { "bool" => true } } },
      "contains_outside" => { "not" => [{ "contains" => [set.(0, 1), int.(7)] }] },
      "get_outside" => { "eq" => [{ "get" => [map, int.(7)] }, int.(0)] },
      "at_negative" => { "eq" => [{ "at" => [list.(1), int.(-1)] }, int.(0)] },
      "keys_of_map" => { "eq" => [{ "keys" => [map] }, set.(0, 1)] }
    }
    exprs.each do |name, e|
      ir = { "ir_version" => 1, "name" => name,
             "states" => [{ "name" => "n", "type" => { "int" => { "min" => 0, "max" => 0 } }, "initial" => int.(0) }],
             "invariants" => [{ "name" => name, "expr" => e }] }
      compare(ir, name)
    end

    record = { "record" => [{ "name" => "a", "type" => small }, { "name" => "b", "type" => small }] }
    updates = {
      "record_field" => [record, { "record" => [{ "name" => "a", "expr" => int.(1) }, { "name" => "b", "expr" => int.(2) }] }],
      "option_payload" => [{ "option" => small }, { "some" => [int.(2)] }],
      "single_tuple" => [{ "tuple" => [small] }, { "tuple" => [int.(2)] }],
      "tuple_after_set" => [{ "tuple" => [{ "set" => small }, small] }, { "tuple" => [set.(1), int.(-1)] }],
      "map_put_outside" => [{ "map" => { "key" => small, "value" => small } }, { "put" => [map, int.(0), int.(2)] }]
    }
    updates.each do |name, (type, e)|
      ir = { "ir_version" => 1, "name" => name,
             "states" => [{ "name" => "v", "type" => type, "initial" => literal_default(type) }],
             "actions" => [{ "name" => "go", "updates" => [{ "target" => 0, "expr" => e }] }] }
      expected, = compare(ir, name)
      assert_equal "error", expected["status"], name
    end
  end

  def literal_default(type)
    kind, body = type.first
    case kind
    when "int" then { "int" => body["min"] }
    when "record" then { "record" => body.map { |f| { "name" => f["name"], "expr" => literal_default(f["type"]) } } }
    when "tuple" then { "tuple" => body.map { |t| literal_default(t) } }
    when "option" then { "none" => body }
    when "set" then { "set" => { "of" => body, "items" => [] } }
    when "map" then { "map" => { "key" => body["key"], "value" => body["value"], "items" => [] } }
    end
  end

  # 複合型、量化、let、除算を使うモデル。エンジンはスロットの列に下ろして検査し、参照実装は値をそのまま扱う。
  def test_random_composite_models
    statuses = Hash.new(0)
    errors = Hash.new(0)
    COUNT.times do |n|
      seed = SEED * 2_000_003 + n
      rng = Random.new(seed)
      generator = CompositeGenerator.new(seed)
      ir = generator.model
      options = { deadlock: rng.rand < 0.3 }
      options[:max_states] = rng.rand(1..20) if rng.rand < 0.1
      with_depth(options, seed)
      expected, path, cert = compare(ir, "composite seed #{seed}", **options)
      statuses[expected["status"]] += 1
      errors[expected["property"]["error"]["kind"]] += 1 if expected["status"] == "error"
      if expected["status"] == "verified"
        compare_certificates(ir, expected, path, cert, rng, options) { generator_state(generator, ir) }
      end
      compare_simulation(ir, path, rng, options.except(:max_states, :max_depth))
    end
    %w[verified violated error].each { |s| assert_operator statuses[s], :>, COUNT / 30, "結果の分布: #{statuses}" }
    # 失敗の種類も、ひととおり試す。
    %w[none missing_key index_out_of_range full empty not_in_domain out_of_range].each do |kind|
      assert_operator errors[kind], :>, 0, "失敗の分布: #{errors}"
    end
  end

  # 一部のモデルに深さの上限を付ける。モデルと他の検査条件の生成の乱数列を変えないよう、別の乱数を使う。
  def with_depth(options, seed)
    rng = Random.new(seed ^ 0x5DEECE66D)
    options[:max_depth] = rng.rand(0..4) if rng.rand < 0.2
  end

  def generator_state(generator, ir)
    ir["states"].map { |s| generator.json_of(s["type"], bad: true) }
  end

  # 同じ seed のシミュレーションが、同じトレースをたどることを確かめる。
  def compare_simulation(ir, path, rng, options)
    sim = { seed: rng.rand(2**64), traces: rng.rand(1..8), max_steps: rng.rand(0..12) }
    expected = reference(ir).simulate(**sim, **options)
    actual, code = cli("simulate", path, "--seed", sim[:seed].to_s, "--traces", sim[:traces].to_s,
                       "--max-steps", sim[:max_steps].to_s, *flags(**options))
    context = -> { "#{JSON.generate(ir)}\noptions: #{options} #{sim}\nreference: #{expected}\nengine: #{actual}" }
    assert_equal expected["status"], actual["status"], context
    assert_equal({ "sampled" => 0, "violated" => 1, "error" => 2 }.fetch(expected["status"]), code, context)
    assert_equal expected["completed_traces"], actual["simulation"]["completed_traces"], context
    assert_equal expected["total_steps"], actual["simulation"]["steps"], context
    return if expected["status"] == "sampled"

    assert_equal expected["property"], actual["property"].except("source"), context
    assert_equal expected["initial"], actual["trace"]["initial"], context
    assert_equal expected["steps"], actual["trace"]["steps"], context
  end

  # 証明書を崩して、受理・拒否とその理由を比べる。
  def compare_certificates(ir, expected, path, cert, rng, options, &make_state)
    m = reference(ir)
    cert_options = options.except(:max_states, :max_depth)
    variants = [expected["certificate"]]
    variants << expected["certificate"].reject { rng.rand < 0.4 }
    make_state ||= -> { random_state(ir, rng) }
    variants << (expected["certificate"] + Array.new(3) { make_state.call }).uniq
    document = JSON.parse(File.read(cert, encoding: Encoding::UTF_8))
    variants.each do |states|
      File.write(cert, JSON.generate(document.merge("states" => states)))
      reason = m.reject_certificate(states.map { |row| m.state_from_json(row) }, **cert_options)
      actual, code = cli("verify-certificate", path, cert, *flags(**cert_options))
      context = -> { "#{JSON.generate(ir)}\noptions: #{cert_options}\nstates: #{states}\nengine: #{actual}" }
      if reason
        assert_equal ["rejected", reason, 1], [actual["status"], actual.dig("rejected", "reason"), code], context
      else
        assert_equal ["verified", 0], [actual["status"], code], context
      end
    end
  end

  # 状態型に従う値を主に、ときどき範囲外の整数を混ぜた状態。
  def random_state(ir, rng)
    ir["states"].map do |s|
      type = s["type"]
      if type.key?("int")
        range = type["int"]
        rng.rand < 0.1 ? range["max"] + 1 : rng.rand(range["min"]..range["max"])
      elsif type.key?("bool")
        rng.rand < 0.5
      else
        variants = ir["enums"].find { |e| e["name"] == type["enum"] }["variants"]
        variants[rng.rand(variants.length)]
      end
    end
  end
end
