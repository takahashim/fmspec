# frozen_string_literal: true

require_relative "test_helper"
require_relative "model_generator"
require "open3"
require "tmpdir"

# 参照実装と `fmspec` コマンドの結果を突き合わせる（仕様書 §14.3）。
# 探索器、IRの読み込み、結果の直列化は証明の対象外なので、ここで検査する。
#
#   FMSPEC_BIN   比較する実行ファイル（既定は target/debug/fmspec）
#   FMSPEC_FUZZ  ランダム生成するモデルの数（既定は300）
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
    [JSON.parse(out), status.exitstatus]
  end

  def flags(deadlock: false, max_states: nil, actions: nil)
    list = []
    list << "--deadlock" if deadlock
    list += ["--max-states", max_states.to_s] if max_states
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
      assert_equal expected["certificate"], JSON.parse(File.read(cert))["states"], context
    when "violated", "error"
      assert_equal expected["property"], actual["property"].except("source"), context
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
      expected, path, cert = compare(ir, "seed #{seed}", **options)
      statuses[expected["status"]] += 1
      compare_certificates(ir, expected, path, cert, rng, options) if expected["status"] == "verified"
      compare_simulation(ir, path, rng, options.except(:max_states))
    end
    # 生成器が片寄って、どれかの結果をまったく試していない、ということがないようにする。
    %w[verified violated error].each { |s| assert_operator statuses[s], :>, COUNT / 30, "結果の分布: #{statuses}" }
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
    assert_equal expected["steps"], actual["trace"]["steps"], context
  end

  # 証明書を崩して、受理・拒否とその理由を比べる。
  def compare_certificates(ir, expected, path, cert, rng, options)
    m = reference(ir)
    cert_options = options.except(:max_states)
    variants = [expected["certificate"]]
    variants << expected["certificate"].reject { rng.rand < 0.4 }
    variants << (expected["certificate"] + Array.new(3) { random_state(ir, rng) }).uniq
    document = JSON.parse(File.read(cert))
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
