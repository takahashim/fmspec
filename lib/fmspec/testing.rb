# frozen_string_literal: true

module Fmspec
  # `assert_passed!` が、成功しなかったテスト実行に対して raise する。
  class TestFailed < Error
    attr_reader :result

    def initialize(result)
      @result = result
      super(result.to_s)
    end
  end

  # Model-Based Testing の結果（仕様書 §11.2）。
  #
  # 実装に対する有限回のテストの成功であり、形式証明ではない。モデル検査の :verified とは別のものである。
  class TestResult
    # 実行した1ステップ。args は、公開引数と、注入した内部選択の値。
    # output と observation は、実装から得た Ruby の値。
    Step = Struct.new(:action, :args, :output, :observation)

    STATUSES = %i[passed conformance_failure execution_error setup_error model_error model_violation inconclusive].freeze

    attr_reader :status, :seed, :cases, :matched_steps, :steps, :original_steps, :detail, :exception

    def initialize(model:, binding:, status:, seed:, cases:, matched_steps:, steps: [], original_steps: nil, detail: nil,
                   exception: nil, case_seed: nil, coverage: nil)
      @model = model
      @binding = binding
      @status = status
      @seed = seed
      @case_seed = case_seed
      @cases = cases
      @matched_steps = matched_steps
      @steps = steps
      @original_steps = original_steps
      @detail = detail
      @exception = exception
      @coverage = coverage
    end

    STATUSES.each do |name|
      define_method(:"#{name}?") { status == name }
    end

    # 失敗したケースの seed。
    attr_reader :case_seed

    # 失敗に至る操作列。`Model#test(binding, replay: result.inputs)` で再実行できる。
    def inputs = steps.map { |s| [s.action, s.args] }

    # テストが確実に通ったモデルの状態と遷移を、到達可能な状態と遷移と比べる（仕様書 §11.3）。
    # 到達可能な状態と遷移は、呼び出したときに探索する。`max_states` はその探索の状態数の上限。
    # 縮小や再実行の試行は数えない。
    def coverage(max_states: nil)
      raise ArgumentError, "この結果はカバレッジを記録していません" unless @coverage

      @coverage.call(max_states)
    end

    # :inconclusive の理由。
    def reason = detail && detail["reason"]&.to_sym

    # 成功でなければ TestFailed を raise する。未完了のケースを含む実行は成功ではない。
    def assert_passed!
      raise TestFailed, self unless passed?

      self
    end

    def to_s = Report.new(@model, @binding, self).to_s
    def inspect = "#<Fmspec::TestResult #{status}>"
  end

  # テスト結果の人間向けの報告。
  class Report
    HEADINGS = {
      conformance_failure: "Conformance failure",
      execution_error: "Execution error",
      setup_error: "Setup error",
      model_error: "Model error",
      model_violation: "Model violation",
      inconclusive: "Inconclusive"
    }.freeze

    def initialize(model, binding, result)
      @model = model
      @binding = binding
      @result = result
    end

    def to_s
      r = @result
      return "Passed: #{@model.name}（#{r.cases} ケース、照合済み #{r.matched_steps} ステップ、seed #{r.seed}）\n" if r.passed?

      lines = ["#{HEADINGS.fetch(r.status)}: #{@model.name}#{subject}"]
      lines << "  seed: #{r.seed}#{r.case_seed && r.case_seed != r.seed ? "（ケースの seed: #{r.case_seed}）" : ''}"
      r.steps.each_with_index { |s, i| lines << "  #{i + 1}. #{s.action}(#{pairs(s.args)})" }
      lines << "  （縮小前は #{r.original_steps} ステップ）" if r.original_steps && r.original_steps > r.steps.length
      lines.concat(details)
      lines.join("\n") + "\n"
    end

    private

    def pairs(hash) = hash.map { |k, v| "#{k}: #{v.inspect}" }.join(", ")

    def mismatch = @result.detail&.fetch("mismatch", nil) || []

    def subject
      case @result.status
      when :conformance_failure then " / #{mismatch.empty? ? 'observation' : mismatch.join(', ')}"
      when :inconclusive then "（#{@result.reason}）"
      when :model_violation, :model_error then " / #{@result.detail.dig('property', 'name') || @result.detail.dig('property', 'action')}"
      else ""
      end
    end

    def details
      r = @result
      case r.status
      when :conformance_failure then conformance + locations
      when :execution_error, :setup_error
        ["  #{r.exception.class}: #{r.exception.message}"] + locations
      when :inconclusive
        if r.reason == :incomplete_paths
          ["  #{r.cases} 経路はすべて成功しましたが、テスト経路の探索を打ち切ったので、" \
           "経路は到達可能な状態と入力の組の一部しか覆っていません。成功として扱いません"]
        else
          ["  照合済み #{r.matched_steps} ステップ。未完了のケースを含む実行は、成功として扱いません"]
        end
      else ["  #{JSON.generate(r.detail)}"]
      end
    end

    # 期待した値と、観測した値。一致しなかった項目だけを並べる。
    def conformance
      detail = @result.detail
      fields = mismatch.empty? ? detail["observed"]["state"].keys + (detail["observed"].key?("output") ? ["output"] : []) : mismatch
      last = @result.steps.last
      fields.flat_map do |field|
        expected = detail["expected"].map { |e| field == "output" ? e["output"]&.fetch("value", nil) : e["state"][field] }.uniq
        observed = if field == "output"
                     last ? last.output : nil
                   else
                     last ? last.observation[field.to_sym] : detail["observed"]["state"][field]
                   end
        label = field == "output" ? "return value" : field
        many = expected.length > 1 ? "one of " : ""
        shown = Types.unrepresentable?(observed) ? observed["unrepresentable"] : observed.inspect
        ["  expected #{label}: #{many}#{expected.map(&:inspect).join(', ')}", "  observed #{label}: #{shown}"]
      end
    end

    # 仕様と binding の、失敗に関わる定義の位置。
    def locations
      last = @result.steps.last
      return [] unless last

      action = @model.to_ir["actions"].find { |a| a["name"] == last.action.to_s }
      lines = []
      lines << "  specification: #{action['source']['file']}:#{action['source']['line']}" if action && action["source"]
      observers = mismatch.reject { |f| f == "output" }.filter_map { |f| @binding.observers[f.to_sym]&.source }
      sources = (mismatch.include?("output") || observers.empty? ? [@binding.commands[last.action]&.source] : []) + observers
      sources.compact.uniq.each { |source| lines << "  binding: #{source}" }
      lines
    end
  end

  # 1つのテストケースを実行するドライバ（仕様書 §11.4）。
  #
  # setup、command、observe を実行し、結果の値だけをエンジンのセッションに渡す。
  # 次の入力はセッションが選ぶ。記録した操作列を再実行するときは、各入力が全候補で有効であることを
  # セッションに確かめてから実装に適用する。
  class TestCase
    Outcome = Struct.new(:status, :steps, :matched, :detail, :exception)

    def initialize(model, native, binding, options)
      @model = model
      @native = native
      @binding = binding
      @options = options
      # 型。エンジンとやりとりするJSONの値と、command と observe の Ruby の値を、型に従って変換する。
      ir = model.to_ir
      enums = (ir["enums"] || []).to_h { |e| [e["name"], Types::Enum.new(e["name"].to_sym, e["variants"].map(&:to_sym))] }
      @state_types = ir["states"].to_h { |s| [s["name"].to_sym, Types.from_ir(s["type"], enums)] }
      @arg_types = ir["actions"].to_h do |action|
        bindings = action["params"] + action["choices"]
        [action["name"].to_sym, bindings.to_h { |b| [b["name"].to_sym, Types.from_ir(b["type"], enums)] }]
      end
      @output_types = ir["actions"].to_h do |action|
        [action["name"].to_sym, action["output"] && Types.from_ir(action["output"]["type"], enums)]
      end
    end

    # `seed` で入力を選びながら、最大 `max_steps` ステップ実行する。
    def generate(seed, max_steps, collector = nil)
      run(seed, collector) do |session, steps|
        next nil if steps.length >= max_steps

        answer = ask(session.next_input)
        case answer["status"]
        when "input" then decode(answer["action"], answer["args"].merge(answer["choices"]))
        when "end" then nil
        else throw :finished, outcome(answer["status"].to_sym, steps, answer)
        end
      end
    end

    # 記録した操作列を再実行する。入力がどれかの候補で無効なら、実装に適用せずに :invalid で終える。
    def replay(inputs, collector = nil)
      run(0, collector) do |session, steps|
        input = inputs[steps.length]
        next nil unless input

        input = normalize(*input)
        answer = ask(session.check_input(JSON.generate(wire_input(*input))))
        case answer["status"]
        when "valid" then input
        when "invalid" then throw :finished, outcome(:invalid, steps, answer)
        else throw :finished, outcome(answer["status"].to_sym, steps, answer)
        end
      end
    end

    # 注入する内部選択。操作名から、内部選択の名前の配列。
    def inject
      @binding.commands.reject { |_, h| h.inject.empty? }.to_h { |name, h| [name.to_s, h.inject.map(&:to_s)] }
    end

    # モデル検査のトレースを、再実行する操作列にする。内部選択は、binding が注入するものだけを入力に含める。
    def trace_inputs(trace)
      trace.steps.map do |step|
        handler = @binding.commands.fetch(step.action) { raise ArgumentError, "トレースの操作 #{step.action} の command がありません" }
        decode(step.action, step.args.merge(step.choices.slice(*handler.inject.map(&:to_s))))
      end
    end

    # エンジンが返した入力（`{"action", "args", "choices"}`）を、[操作名, キーワード引数] にする。
    def decode_input(input) = decode(input["action"], input["args"].merge(input["choices"]))

    private

    # エンジンが選んだ入力（JSON）を、[操作名, キーワード引数] にする。値は型に従って Ruby の値にする。
    def decode(action, args)
      action = action.to_sym
      types = arg_types(action)
      [action, args.to_h { |name, value| [name.to_sym, types.fetch(name.to_sym).from_wire(value)] }]
    end

    # 記録した入力を、[操作名, キーワード引数] にそろえる。列挙型のラベルは Symbol にする。
    def normalize(action, args)
      action = action.to_sym
      types = arg_types(action)
      [action, (args || {}).to_h do |name, value|
        [name.to_sym, types[name.to_sym].is_a?(Types::Enum) && value.is_a?(String) ? value.to_sym : value]
      end]
    end

    def arg_types(action) = @arg_types.fetch(action) { raise ArgumentError, "未定義の操作 #{action}" }

    def run(seed, collector, &next_input)
      context = begin
        @binding.setup_block.call
      rescue StandardError => e
        return Outcome.new(:setup_error, [], 0, nil, e)
      end
      scheduler = Scheduler.new(@binding, context) unless @binding.processes.empty?
      result = begin
        start(scheduler) || catch(:finished) { drive(context, scheduler, seed, collector, &next_input) }
      ensure
        failed = [stop(scheduler), teardown(context)].compact.first
      end
      failed || result
    end

    # プロセスのスレッドの setup を待つ。失敗は setup の失敗として報告する。
    def start(scheduler)
      scheduler&.start
      nil
    rescue StandardError => e
      Outcome.new(:setup_error, [], 0, nil, e)
    end

    # プロセスのスレッドを終える。teardown の失敗は、隔離の失敗として報告する。
    def stop(scheduler)
      error = scheduler&.stop
      error && Outcome.new(:setup_error, [], 0, nil, error)
    end

    # teardown の失敗は、隔離の失敗として報告する。成功として扱わない。
    def teardown(context)
      @binding.teardown_block&.call(context)
      nil
    rescue StandardError => e
      Outcome.new(:setup_error, [], 0, nil, e)
    end

    def drive(context, scheduler, seed, collector)
      options = @options.merge("seed" => seed, "observe" => @binding.observers.keys.map(&:to_s), "inject" => inject)
      session = Native::Session.start(@native, JSON.generate(options))
      raise ArgumentError, JSON.parse(session)["message"] if session.is_a?(String)

      steps = []
      observation = observe(context, steps)
      answer = ask(session.initial(JSON.generate(wire(observation))))
      return outcome(answer["status"].to_sym, steps, answer) unless answer["status"] == "continue"

      collector&.initial(answer["covered"])
      while (input = yield(session, steps))
        action, args = input
        output = begin
          execute(context, scheduler, action, args)
        rescue Scheduler::StepTimeout => e
          steps << TestResult::Step.new(action, args, nil, nil)
          return Outcome.new(:inconclusive, steps, steps.length - 1, { "reason" => "step_timeout", "action" => action.to_s }, e)
        rescue StandardError => e
          steps << TestResult::Step.new(action, args, nil, nil)
          return Outcome.new(:execution_error, steps, steps.length - 1, nil, e)
        end
        steps << TestResult::Step.new(action, args, output, nil)
        observation = observe(context, steps)
        steps.last.observation = observation
        report = wire_input(action, args).merge("output" => wire_output(action, output), "observation" => wire(observation))
        answer = ask(session.observe(JSON.generate(report)))
        return outcome(answer["status"].to_sym, steps, answer) unless answer["status"] == "continue"

        collector&.step(action, answer["covered"])
      end
      Outcome.new(:passed, steps, steps.length, nil, nil)
    end

    # command を実行する。プロセスのステップは、そのインスタンスのスレッドで実行する。
    def execute(context, scheduler, action, args)
      handler = @binding.commands.fetch(action)
      return scheduler.run(handler, args) if handler.worker

      handler.callable.call(context, **args)
    end

    def observe(context, steps)
      @binding.observers.transform_values { |handler| handler.callable.call(context) }
    rescue StandardError => e
      throw :finished, Outcome.new(:execution_error, steps, [steps.length - 1, 0].max, nil, e)
    end

    def outcome(status, steps, answer)
      matched = status == :conformance_failure || status == :invalid ? [steps.length - 1, 0].max : steps.length
      Outcome.new(status, steps, answer["matched"] || matched, answer, nil)
    end

    def ask(json)
      answer = JSON.parse(json)
      raise ArgumentError, answer["message"] if answer["status"] == "usage_error"

      answer
    end

    # 入力を、公開引数（args）と注入する選択（choices）に分ける。
    def wire_input(action, args)
      injected = @binding.commands.fetch(action).inject
      types = arg_types(action)
      choices, params = args.partition { |name, _| injected.include?(name) }.map(&:to_h)
      wire_args = ->(h) { h.to_h { |name, v| [name, types[name] ? types[name].to_wire(v) : Types.unrepresentable(v)] } }
      { "action" => action, "args" => wire_args.(params), "choices" => wire_args.(choices) }
    end

    # 実装から得た値を、型に従ってエンジンに渡せる形にする。
    # 仕様の値にならないものは、どの値とも一致しないJSONにするので、不適合として報告される。
    def wire(observation)
      observation.to_h { |name, value| [name.to_s, @state_types.fetch(name).to_wire(value)] }
    end

    # 出力を宣言しない操作の戻り値は比べないので、何を渡してもよい。
    def wire_output(action, output)
      type = @output_types.fetch(action)
      type ? type.to_wire(output) : nil
    end
  end

  # テスト経路（`Model#test_paths` の結果）。操作列の配列で、経路を作った探索の報告を持つ。
  class TestPaths < Array
    # 経路で覆う対象（状態と入力の組で、有効な遷移があるもの）の数と、経路が覆った数。
    attr_reader :targets, :covered

    def initialize(paths, complete:, targets:, covered:)
      super(paths)
      @complete = complete
      @targets = targets
      @covered = covered
    end

    # 到達可能な状態をすべて探索したか。偽なら（状態数の上限か評価エラーで打ち切った）、
    # 経路は到達可能な状態と入力の組の一部しか覆っていない。`Model#test(paths:)` は、全経路が成功しても
    # :passed にせず、:inconclusive（理由は :incomplete_paths）にする。
    def complete? = @complete
  end

  # テスト実行の全体。ケースを順に実行し、最初の失敗を縮小して報告する。
  class TestRun
    FAILURES = %i[conformance_failure execution_error].freeze

    def initialize(model, native, binding, cases:, steps:, seed:, shrink:, shrink_runs:, options:)
      @model = model
      @native = native
      @binding = binding
      @options = options
      @case = TestCase.new(model, native, binding, options)
      @collector = Coverage::Collector.new
      @cases = cases
      @steps = steps
      @seed = seed
      @shrink = shrink
      @shrink_runs = shrink_runs
    end

    def run
      matched = 0
      inconclusive = nil
      @cases.times do |i|
        case_seed = (@seed + i) % (2**64)
        outcome = @case.generate(case_seed, @steps, @collector)
        matched += outcome.matched
        next if outcome.status == :passed

        if outcome.status == :inconclusive
          inconclusive ||= [outcome, case_seed, i + 1]
          next
        end
        return failure(outcome, case_seed, i + 1, matched)
      end
      return result(inconclusive[0], inconclusive[1], @cases, matched) if inconclusive

      passed(@cases, matched)
    end

    # 記録した操作列を1回だけ再実行する。
    def replay(inputs)
      inputs = @case.trace_inputs(inputs) if inputs.is_a?(Trace)
      outcome = invalid_as_inconclusive(@case.replay(inputs, @collector))
      result(outcome, @seed, 1, outcome.matched)
    end

    # 操作列を1つずつケースとして再実行する。最初の失敗を縮小して報告する。
    # 実装が別の遷移を選んで操作列をたどれなくなったケースは :inconclusive（invalid_input）として記録し、残りを続ける。
    # 探索を打ち切って作ったテスト経路（`TestPaths#complete?` が偽）では、全経路が成功しても :passed にせず、
    # :inconclusive（理由は incomplete_paths）にする。経路は到達可能な状態と入力の組の一部しか覆っていない。
    def run_paths(paths)
      matched = 0
      inconclusive = nil
      paths.each_with_index do |inputs, i|
        outcome = invalid_as_inconclusive(@case.replay(inputs, @collector))
        matched += outcome.matched
        next if outcome.status == :passed

        if outcome.status == :inconclusive
          inconclusive ||= [outcome, i + 1]
          next
        end
        return failure(outcome, @seed, i + 1, matched)
      end
      return result(inconclusive[0], @seed, paths.length, matched) if inconclusive
      if paths.is_a?(TestPaths) && !paths.complete?
        outcome = TestCase::Outcome.new(:inconclusive, [], 0, { "reason" => "incomplete_paths" }, nil)
        return result(outcome, @seed, paths.length, matched)
      end

      passed(paths.length, matched)
    end

    # 到達可能な状態と遷移のグラフを使う結果（カバレッジとテスト経路）のJSONを読む。
    # 使い方の誤りは ArgumentError、探索器の内部の不整合（status が internal_error）は InternalError にする。
    # 不整合はエンジンの不具合で、集めきれなかったグラフをカバレッジの分母やテスト経路に使わない。
    def self.graph_body(json)
      body = JSON.parse(json)
      raise ArgumentError, body["message"] if body["status"] == "usage_error"
      raise InternalError, "#{body['message']}: #{JSON.generate(body['inconsistency'])}" if body["status"] == "internal_error"

      body
    end

    # 到達可能な状態と入力の組を覆う操作列を、モデルから作る。
    def paths(max_steps:, max_states:)
      options = @options.slice("actions").merge("max_steps" => max_steps, "inject" => @case.inject)
      options["max_states"] = max_states if max_states
      body = TestRun.graph_body(@native.test_paths(JSON.generate(options)))
      paths = body["paths"].map { |path| path["inputs"].map { |input| @case.decode_input(input) } }
      TestPaths.new(paths, complete: body["complete"], targets: body["targets"], covered: body["covered"])
    end

    private

    def passed(cases, matched)
      TestResult.new(model: @model, binding: @binding, status: :passed, seed: @seed, cases: cases, matched_steps: matched,
                     coverage: coverage)
    end

    def result(outcome, case_seed, cases, matched, original_steps: nil)
      TestResult.new(model: @model, binding: @binding, status: outcome.status, seed: @seed, case_seed: case_seed,
                     cases: cases, matched_steps: matched, steps: outcome.steps, original_steps: original_steps,
                     detail: outcome.detail, exception: outcome.exception, coverage: coverage)
    end

    def invalid_as_inconclusive(outcome)
      return outcome unless outcome.status == :invalid

      TestCase::Outcome.new(:inconclusive, outcome.steps, outcome.matched, { "reason" => "invalid_input" }, outcome.exception)
    end

    # 記録した状態と遷移から、カバレッジを作る関数。探索は呼び出したときに行う。
    def coverage
      collected = @collector
      options = @options.slice("actions")
      native = @native
      lambda do |max_states|
        request = options.merge("seen" => collected.seen)
        request["max_states"] = max_states if max_states
        Coverage.new(TestRun.graph_body(native.coverage(JSON.generate(request))), collected)
      end
    end

    def failure(outcome, case_seed, cases, matched)
      return result(outcome, case_seed, cases, matched) unless @shrink && FAILURES.include?(outcome.status)

      shrunk = shrink(outcome)
      result(shrunk, case_seed, cases, matched, original_steps: outcome.steps.length)
    end

    # 縮小で保つ、失敗の識別子（仕様書 §10）。種別と、失敗した操作、一致しなかった項目または例外のクラス。
    def identity(outcome)
      what = outcome.status == :conformance_failure ? outcome.detail["mismatch"] : outcome.exception.class
      [outcome.status, outcome.steps.last&.action, what]
    end

    # 実装不適合の縮小。操作列からステップを削った候補を、新しい実装のコンテキストで再実行し、
    # 同じ識別子の失敗が起きる候補を採用する。結果は局所最小である。
    def shrink(original)
      best = original
      wanted = identity(original)
      runs = @shrink_runs
      chunk = [(best.steps.length + 1) / 2, 1].max
      loop do
        start = 0
        removed = false
        while start < best.steps.length && runs.positive?
          runs -= 1
          inputs = best.steps.map { |s| [s.action, s.args] }
          candidate = @case.replay(inputs[0...start] + (inputs[(start + chunk)..] || []))
          if FAILURES.include?(candidate.status) && identity(candidate) == wanted
            best = candidate
            removed = true
          else
            start += chunk
          end
        end
        return best if runs.zero? || (chunk == 1 && !removed)

        chunk = (chunk + 1) / 2 unless removed
        chunk = [[chunk, best.steps.length].min, 1].max
      end
    end
  end
end
