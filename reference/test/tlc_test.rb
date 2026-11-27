# frozen_string_literal: true

require_relative "test_helper"
require_relative "model_generator"
require_relative "../fmspec_tla"
require "open3"
require "tmpdir"
require "fileutils"

# fmspec の結果を、TLA+ に変換したモデルを TLC で検査した結果と突き合わせる。
# 参照実装との比較テスト（differential_test.rb）は、同じ作者が書いた2つの実装を比べる。
# このテストは、意味論の解釈を、独立に実装された TLC の評価器と状態空間の探索に照らして確かめる。
#
# TLC は到達できる状態をすべて書き出す（変換の仕方は fmspec_tla.rb）。
# 書き出された状態から、fmspec の安全性の意味での事象（不変条件の違反と評価エラー、
# 遷移契約の違反と評価エラー、操作の適用の評価エラー、デッドロック、終端条件の評価エラー）を集め、次を確かめる。
#
# - fmspec が verified なら、事象は1つもなく、到達できる状態の集合が証明書の状態の集合と一致する。
# - fmspec が violated か error なら、トレースの状態はどれも到達でき、末尾の主張は TLC の事象の1つである。
#
# どの事象を報告するか、反例がどれだけ短いかは探索の順序で決まり、参照実装との比較テストが検査する。
#
#   TLA2TOOLS    tla2tools.jar のパス（必須。なければ skip）
#   JAVA         java の実行ファイル（既定は java）
#   FMSPEC_BIN   比較する実行ファイル（既定は target/debug/fmspec）
#   FMSPEC_TLC   ランダム生成するモデルの数（既定は200）
#   FMSPEC_SEED  生成の種（既定は1）
#   TLC_JOBS     同時に実行する TLC の数（既定は4）
#   TLC_TIMEOUT  TLC の1回の実行の時間の上限（秒、既定は120）
class TlcTest < Minitest::Test
  BIN = ENV.fetch("FMSPEC_BIN", File.join(ROOT, "target/debug/fmspec"))
  JAR = ENV.fetch("TLA2TOOLS", "")
  JAVA = ENV.fetch("JAVA", "java")
  COUNT = Integer(ENV.fetch("FMSPEC_TLC", "200"))
  SEED = Integer(ENV.fetch("FMSPEC_SEED", "1"))
  JOBS = Integer(ENV.fetch("TLC_JOBS", "4"))
  TLC_TIMEOUT = Integer(ENV.fetch("TLC_TIMEOUT", "120"))

  def setup
    skip "環境変数 TLA2TOOLS に tla2tools.jar のパスを指定してください" unless File.file?(JAR)
    skip "#{BIN} がありません。先に cargo build を実行してください" unless File.executable?(BIN)
    @dir = Dir.mktmpdir("fmspec-tlc")
  end

  def teardown
    FileUtils.remove_entry(@dir) if @dir
  end

  # ---- 実行 ----

  Job = Struct.new(:label, :ir, :options, :dir, :engine, :certificate, :tlc, keyword_init: true)

  def job(label, ir, options = {})
    dir = File.join(@dir, "job#{@jobs_made = (@jobs_made || 0) + 1}")
    FileUtils.mkdir_p(dir)
    translator = FmspecTla::Translator.new(ir, actions: options[:actions], contracts: options[:contracts])
    File.write(File.join(dir, "M.tla"), translator.module_text)
    File.write(File.join(dir, "M.cfg"), translator.cfg_text)
    Job.new(label: label, ir: ir, options: options, dir: dir)
  end

  def flags(options)
    list = []
    list << "--deadlock" if options[:deadlock]
    %i[actions invariants contracts].each { |k| list += ["--#{k}", options[k].join(",")] if options[k] }
    list
  end

  def run_engine(job)
    path = File.join(job.dir, "model.json")
    cert = File.join(job.dir, "certificate.json")
    File.write(path, JSON.generate(job.ir))
    out, = Open3.capture2(BIN, "check", path, "--json", "--certificate-out", cert, *flags(job.options))
    job.engine = JSON.parse(out.force_encoding(Encoding::UTF_8))
    job.certificate = JSON.parse(File.read(cert, encoding: Encoding::UTF_8))["states"] if File.exist?(cert)
  end

  def run_tlc(job)
    # TLC v1.7.4 は標準モジュールを java.io.tmpdir に書き出す。並べて実行すると読み込みが衝突するので、実行ごとに分ける。
    tmp = File.join(job.dir, "java-tmp")
    FileUtils.mkdir_p(tmp)
    command = [JAVA, "-XX:+UseSerialGC", "-Djava.io.tmpdir=#{tmp}", "-cp", JAR, "tlc2.TLC", "-workers", "1", "-deadlock",
               "-dump", "states", "-metadir", "meta", "-nowarning", "M"]
    out, status = Open3.popen2e(*command, chdir: job.dir) do |stdin, output, wait|
      stdin.close
      reader = Thread.new { output.read }
      # 変換の誤りで状態空間が有限でなくなると、TLC は止まらない。
      unless wait.join(TLC_TIMEOUT)
        Process.kill("KILL", wait.pid)
        wait.join
        return job.tlc = { "failed" => "#{TLC_TIMEOUT}秒で終わらなかった\n#{reader.value}" }
      end
      [reader.value, wait.value]
    end
    unless status.success? && out.include?("Model checking completed. No error has been found.")
      return job.tlc = { "failed" => out }
    end

    found = Integer(out[/(\d+) distinct states found/, 1])
    states = FmspecTla::Dump.parse(File.read(File.join(job.dir, "states.dump"), encoding: Encoding::UTF_8))
    job.tlc = { "distinct" => found, "states" => states }
  end

  # TLC を JOBS 個ずつ並べて実行する。JVM の起動が実行時間の大半を占める。
  def run_all(jobs)
    jobs.each { |j| run_engine(j) }
    queue = Queue.new
    jobs.each { |j| queue << j }
    Array.new(JOBS) do
      Thread.new do
        while (j = begin
          queue.pop(true)
        rescue ThreadError
          nil
        end)
          run_tlc(j)
        end
      end
    end.each(&:join)
    jobs.map { |j| compare(j) }
  end

  # ---- 比較 ----

  def state_names(ir)
    ir["states"].map { |s| s["name"] }
  end

  def row(ir, json)
    json.is_a?(Hash) ? state_names(ir).map { |n| json.fetch(n) } : json
  end

  def binding_row(bindings, json)
    (bindings || []).map { |b| json.fetch(b["name"]) }
  end

  # TLC の状態から、fmspec の安全性の意味での事象を集める。
  def tlc_events(job)
    ir = job.ir
    opts = job.options
    n = ir["states"].length
    invariants = ir["invariants"] || []
    targets = opts[:invariants] || invariants.map { |i| i["name"] }
    reachable = []
    events = []
    job.tlc["states"].each do |s|
      values = Array.new(n) { |i| s.fetch("v#{i}") }
      bad = s.fetch("bad")
      if bad.empty?
        reachable << values
        obs = s.fetch("obs")
        failing = invariants.each_with_index.find { |inv, i| targets.include?(inv["name"]) && obs[i] != "true" }
        if failing
          inv, i = failing
          events << [:invariant, values, inv["name"], obs[i]]
        end
        enabled, terminal = obs.last(2)
        events << [:deadlock, values, terminal] if opts[:deadlock] && !enabled && terminal != "true"
      elsif bad[0] == "apply"
        _, action, params, choices, site, target, kind, value = bad
        events << [:apply, values, action, params, choices, site, target, kind, value]
      else
        _, action, params, choices, name, result = bad
        events << [:contract, values, action, params, choices, name, result]
      end
    end
    [reachable, events]
  end

  def result_of(property)
    property.key?("violation") ? "false" : property["error"]["kind"]
  end

  # fmspec の報告した事象を、tlc_events と同じ形にする。
  def engine_event(job)
    ir = job.ir
    trace = job.engine["trace"]
    prop = job.engine["property"]
    initial = trace["initial"] ? row(ir, trace["initial"]) : nil
    states = [initial, *trace["steps"].map { |st| row(ir, st["state"]) }]
    last = states.last
    case prop["site"] || prop["violation"]
    when "invariant" then [:invariant, last, prop["name"], result_of(prop)]
    when "deadlock" then [:deadlock, last, "false"]
    when "terminal" then [:deadlock, last, result_of(prop)]
    when "contract"
      step = trace["steps"].last
      action = ir["actions"].find { |a| a["name"] == step["action"] }
      [:contract, states[-2], step["action"], binding_row(action["params"], step["args"]),
       binding_row(action["choices"], step["choices"]), prop["name"], result_of(prop)]
    else
      action = ir["actions"].find { |a| a["name"] == prop["action"] }
      error = prop["error"]
      value = error["kind"] == "out_of_range" ? error["value"] : 0
      [:apply, last, prop["action"], binding_row(action["params"], prop["args"]),
       binding_row(action["choices"], prop["choices"]), prop["site"], prop["target"] || "", error["kind"], value]
    end.then { |event| [event, states] }
  end

  def compare(job)
    context = lambda do
      "#{job.label}\n#{JSON.generate(job.ir)}\noptions: #{job.options}\nengine: #{JSON.generate(job.engine)}\n" \
        "tlc: #{job.tlc['failed'] || job.tlc['states'].length}"
    end
    refute job.tlc.key?("failed"), -> { "TLC が失敗した\n#{context.call}\n#{job.tlc['failed']}" }
    assert_equal job.tlc["distinct"], job.tlc["states"].length, context
    reachable, events = tlc_events(job)
    case job.engine["status"]
    when "verified"
      assert_empty events, context
      assert_equal reachable.sort_by(&:inspect), job.certificate.map { |r| row(job.ir, r) }.sort_by(&:inspect), context
    when "violated", "error"
      event, states = engine_event(job)
      # 初期状態が1つのモデルでは、トレースの開始状態を省略できる。
      states = states.drop(1) if states.first.nil?
      states.each { |s| assert_includes reachable, s, context }
      assert_includes events, event, context
    else
      flunk "想定外の結果\n#{context.call}"
    end
    job.engine["status"]
  end

  # ---- テスト ----

  def int(n) = { "int" => n }

  def single(name, expr)
    { "ir_version" => 1, "name" => name,
      "states" => [{ "name" => "n", "type" => { "int" => { "min" => 0, "max" => 0 } }, "initial" => int(0) }],
      "invariants" => [{ "name" => name, "expr" => expr }] }
  end

  def test_fixed_models
    models = {
      "tickets" => Models.tickets,
      "tickets_without_guard" => Models.tickets_without_guard,
      "responder" => Models.responder,
      "stuck" => Models.counter(0, []),
      "loop" => Models.counter(1, [Models.stay, Models.go("go", 0, 1)])
    }
    jobs = models.flat_map do |name, ir|
      [false, true].map { |deadlock| job(name, ir, deadlock: deadlock) }
    end
    run_all(jobs)
  end

  # 床除算、評価の順序、打ち切り、量化の順序など、TLA+ と既定の意味が違うところ。
  def test_boundary_expressions
    zero_div = { "eq" => [{ "div" => [int(1), int(0)] }, int(0)] }
    small = { "int" => { "min" => -1, "max" => 1 } }
    exprs = {}
    [[-7, 2], [7, -2], [-7, -2], [7, 2], [0, -3], [-6, 3], [-6, -3]].each do |a, b|
      q = a.fdiv(b).floor
      exprs["div_#{a}_#{b}"] = { "eq" => [{ "div" => [int(a), int(b)] }, int(q)] }
      exprs["mod_#{a}_#{b}"] = { "eq" => [{ "mod" => [int(a), int(b)] }, int(a - (b * q))] }
    end
    exprs.merge!(
      "div_by_zero" => zero_div,
      "mod_by_zero" => { "eq" => [{ "mod" => [int(1), int(0)] }, int(0)] },
      "left_error_first" => { "lt" => [{ "div" => [int(1), int(0)] }, { "mod" => [int(1), int(0)] }] },
      "all_stops" => { "all" => [{ "bool" => false }, zero_div] },
      "all_error_first" => { "all" => [zero_div, { "bool" => false }] },
      "any_stops" => { "any" => [{ "bool" => true }, zero_div] },
      "implies_skips" => { "implies" => [{ "bool" => false }, zero_div] },
      "ite_skips" => { "ite" => [{ "bool" => true }, { "bool" => true }, zero_div] },
      "let_is_eager" => { "let" => { "name" => "y", "value" => { "div" => [int(1), int(0)] }, "body" => { "bool" => true } } },
      "let_binds" => { "let" => { "name" => "y", "value" => int(3),
                                  "body" => { "eq" => [{ "local" => "y" }, int(3)] } } },
      "forall_order" => { "forall" => { "name" => "x", "type" => small,
                                        "body" => { "ite" => [{ "eq" => [{ "local" => "x" }, int(1)] }, zero_div,
                                                              { "ne" => [{ "local" => "x" }, int(0)] }] } } },
      "exists_order" => { "exists" => { "name" => "x", "type" => { "bool" => {} },
                                        "body" => { "ite" => [{ "local" => "x" }, zero_div, { "bool" => true }] } } }
    )
    run_all(exprs.map { |name, e| job(name, single(name, e)) })
  end

  # 範囲外更新、更新と出力の順序、遷移契約、定数、初期条件。
  def test_boundary_transitions
    bit = { "int" => { "min" => 0, "max" => 1 } }
    two = lambda do |actions, extra = {}|
      { "ir_version" => 1, "name" => "two",
        "constants" => [{ "name" => "one", "type" => bit, "value" => int(1) }],
        "states" => [{ "name" => "a", "type" => bit, "initial_in" => [int(0), int(1)] },
                     { "name" => "b", "type" => bit, "initial" => int(0) }],
        "actions" => actions }.merge(extra)
    end
    jobs = []
    jobs << job("out_of_range_second", two.([{ "name" => "go", "updates" => [
      { "target" => 1, "expr" => { "add" => [{ "var" => 1 }, int(2)] } },
      { "target" => 0, "expr" => { "div" => [int(1), int(0)] } }
    ] }]))
    jobs << job("output_after_updates", two.([{ "name" => "go", "output" => { "type" => bit, "expr" => int(5) },
                                                "updates" => [{ "target" => 0, "expr" => int(3) }] }]))
    jobs << job("output_range", two.([{ "name" => "go", "output" => { "type" => bit, "expr" => { "const" => "one" } },
                                        "params" => [{ "name" => "p", "type" => bit }],
                                        "guard" => { "eq" => [{ "var" => 0 }, { "param" => 0 }] },
                                        "updates" => [{ "target" => 0, "expr" => { "sub" => [{ "const" => "one" }, { "var" => 0 }] } }] }],
                                     "contracts" => [{ "name" => "flips", "action" => "go",
                                                       "expr" => { "all" => [{ "ne" => [{ "next" => 0 }, { "var" => 0 }] },
                                                                             { "eq" => [{ "output" => {} }, int(1)] },
                                                                             { "eq" => [{ "next" => 1 }, int(1)] }] } }]))
    jobs << job("constraint", two.([], "initial_constraint" => { "eq" => [{ "var" => 0 }, { "const" => "one" }] },
                                       "invariants" => [{ "name" => "a_one", "expr" => { "eq" => [{ "var" => 0 }, int(1)] } }]),
                deadlock: true)
    jobs << job("terminal_error", two.([], "terminal" => { "eq" => [{ "div" => [{ "var" => 0 }, { "var" => 1 }] }, int(0)] }),
                deadlock: true)
    run_all(jobs)
  end

  def test_random_models
    statuses = Hash.new(0)
    skipped = 0
    jobs = []
    COUNT.times do |n|
      seed = SEED * 3_000_017 + n
      rng = Random.new(seed)
      ir = CoreGenerator.new(seed).model
      options = { deadlock: rng.rand < 0.5 }
      names = ->(key) { (ir[key] || []).map { |a| a["name"] } }
      %w[actions invariants contracts].each do |key|
        options[key.to_sym] = names.(key).select { rng.rand < 0.7 } if rng.rand < 0.2
      end
      begin
        jobs << job("seed #{seed}", ir, options)
      rescue FmspecTla::Unsupported
        skipped += 1
      end
    end
    run_all(jobs).each { |s| statuses[s] += 1 }
    # TLC の整数に収まらないモデルを除いても、比べるモデルが十分に残ること。
    assert_operator skipped, :<, COUNT / 3, "変換できなかったモデル: #{skipped}"
    %w[verified violated error].each { |s| assert_operator statuses[s], :>, COUNT / 30, "結果の分布: #{statuses}" }
  end
end

# ModelGenerator に、床除算と剰余、let、型の全体をたどる量化を加えた生成器。
class CoreGenerator < ModelGenerator
  def leaf(want, scope)
    locals = (scope[:locals] || []).select { |_, k| k == want }
    return { "local" => pick(locals)[0] } if !locals.empty? && chance(0.5)

    super
  end

  def expr(want, scope, depth)
    return super if depth.zero? || !chance(0.25)

    sub = ->(k, s = scope) { expr(k, s, depth - 1) }
    case want
    when INT
      case @rng.rand(3)
      when 0, 1 then { pick(%w[div mod]) => [sub.(INT), sub.(INT)] }
      else bind(INT, scope, depth)
      end
    when BOOL
      if chance(0.5)
        bind(BOOL, scope, depth)
      else
        type = chance(0.5) ? { "int" => { "min" => -1, "max" => @rng.rand(-1..2) } } : { "bool" => {} }
        name = "q#{depth}"
        inner = scope.merge(locals: (scope[:locals] || []) + [[name, kind(type)]])
        { pick(%w[forall exists]) => { "name" => name, "type" => type, "body" => sub.(BOOL, inner) } }
      end
    else super
    end
  end

  def bind(want, scope, depth)
    k = pick([INT, BOOL])
    name = "y#{depth}"
    inner = scope.merge(locals: (scope[:locals] || []) + [[name, k]])
    { "let" => { "name" => name, "value" => expr(k, scope, depth - 1), "body" => expr(want, inner, depth - 1) } }
  end
end
