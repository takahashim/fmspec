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
                   exception: nil, case_seed: nil)
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
    end

    STATUSES.each do |name|
      define_method(:"#{name}?") { status == name }
    end

    # 失敗したケースの seed。
    attr_reader :case_seed

    # 失敗に至る操作列。`Model#test(binding, replay: result.inputs)` で再実行できる。
    def inputs = steps.map { |s| [s.action, s.args] }

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
        ["  照合済み #{r.matched_steps} ステップ。未完了のケースを含む実行は、成功として扱いません"]
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
        ["  expected #{label}: #{many}#{expected.map(&:inspect).join(', ')}", "  observed #{label}: #{observed.inspect}"]
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
      # 操作ごとの、列挙型の引数と内部選択の名前。command には、ラベルを Symbol で渡す。
      @enum_args = model.to_ir["actions"].to_h do |action|
        bindings = action["params"] + action["choices"]
        [action["name"].to_sym, bindings.select { |b| b["type"].key?("enum") }.map { |b| b["name"].to_sym }]
      end
    end

    # `seed` で入力を選びながら、最大 `max_steps` ステップ実行する。
    def generate(seed, max_steps)
      run(seed) do |session, steps|
        next nil if steps.length >= max_steps

        answer = ask(session.next_input)
        case answer["status"]
        when "input" then normalize(answer["action"], answer["args"].merge(answer["choices"]))
        when "end" then nil
        else throw :finished, outcome(answer["status"].to_sym, steps, answer)
        end
      end
    end

    # 記録した操作列を再実行する。入力がどれかの候補で無効なら、実装に適用せずに :invalid で終える。
    def replay(inputs)
      run(0) do |session, steps|
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

    private

    # 入力を [操作名, キーワード引数] にそろえる。列挙型の値は Symbol にする。
    def normalize(action, args)
      action = action.to_sym
      enums = @enum_args.fetch(action) { raise ArgumentError, "未定義の操作 #{action}" }
      [action, (args || {}).to_h { |name, value| [name.to_sym, enums.include?(name.to_sym) ? value.to_sym : value] }]
    end

    def run(seed, &next_input)
      context = begin
        @binding.setup_block.call
      rescue StandardError => e
        return Outcome.new(:setup_error, [], 0, nil, e)
      end
      result = begin
        catch(:finished) { drive(context, seed, &next_input) }
      ensure
        failed = teardown(context)
      end
      failed || result
    end

    # teardown の失敗は、隔離の失敗として報告する。成功として扱わない。
    def teardown(context)
      @binding.teardown_block&.call(context)
      nil
    rescue StandardError => e
      Outcome.new(:setup_error, [], 0, nil, e)
    end

    def drive(context, seed)
      inject = @binding.commands.reject { |_, h| h.inject.empty? }.to_h { |name, h| [name.to_s, h.inject.map(&:to_s)] }
      options = @options.merge("seed" => seed, "observe" => @binding.observers.keys.map(&:to_s), "inject" => inject)
      session = Native::Session.start(@native, JSON.generate(options))
      raise ArgumentError, JSON.parse(session)["message"] if session.is_a?(String)

      steps = []
      observation = observe(context, steps)
      answer = ask(session.initial(JSON.generate(wire(observation))))
      return outcome(:conformance_failure, steps, answer) unless answer["status"] == "continue"

      while (input = yield(session, steps))
        action, args = input
        output = begin
          @binding.commands.fetch(action).callable.call(context, **args)
        rescue StandardError => e
          steps << TestResult::Step.new(action, args, nil, nil)
          return Outcome.new(:execution_error, steps, steps.length - 1, nil, e)
        end
        steps << TestResult::Step.new(action, args, output, nil)
        observation = observe(context, steps)
        steps.last.observation = observation
        report = wire_input(action, args).merge("output" => wire_value(output), "observation" => wire(observation))
        answer = ask(session.observe(JSON.generate(report)))
        return outcome(answer["status"].to_sym, steps, answer) unless answer["status"] == "continue"
      end
      Outcome.new(:passed, steps, steps.length, nil, nil)
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
      choices, params = args.partition { |name, _| injected.include?(name) }.map(&:to_h)
      { "action" => action, "args" => params.transform_values { |v| wire_value(v) },
        "choices" => choices.transform_values { |v| wire_value(v) } }
    end

    def wire(observation) = observation.to_h { |name, value| [name.to_s, wire_value(value)] }

    # 実装から得た値を、エンジンに渡せる形にする。仕様の値にならないものは nil にする。
    # nil は仕様のどの値とも一致しないので、不適合として報告される。
    def wire_value(value)
      case value
      when Integer then value.between?(I64_MIN, I64_MAX) ? value : nil
      when true, false, String then value
      when Symbol then value.to_s
      end
    end
  end

  # テスト実行の全体。ケースを順に実行し、最初の失敗を縮小して報告する。
  class TestRun
    FAILURES = %i[conformance_failure execution_error].freeze

    def initialize(model, native, binding, cases:, steps:, seed:, shrink:, shrink_runs:, options:)
      @model = model
      @binding = binding
      @case = TestCase.new(model, native, binding, options)
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
        outcome = @case.generate(case_seed, @steps)
        matched += outcome.matched
        next if outcome.status == :passed

        if outcome.status == :inconclusive
          inconclusive ||= [outcome, case_seed, i + 1]
          next
        end
        return failure(outcome, case_seed, i + 1, matched)
      end
      return result(inconclusive[0], inconclusive[1], @cases, matched) if inconclusive

      TestResult.new(model: @model, binding: @binding, status: :passed, seed: @seed, cases: @cases, matched_steps: matched)
    end

    # 記録した操作列を1回だけ再実行する。
    def replay(inputs)
      outcome = @case.replay(inputs)
      status = outcome.status == :invalid ? :inconclusive : outcome.status
      detail = outcome.status == :invalid ? { "reason" => "invalid_input" } : outcome.detail
      result(TestCase::Outcome.new(status, outcome.steps, outcome.matched, detail, outcome.exception), @seed, 1, outcome.matched)
    end

    private

    def result(outcome, case_seed, cases, matched, original_steps: nil)
      TestResult.new(model: @model, binding: @binding, status: outcome.status, seed: @seed, case_seed: case_seed,
                     cases: cases, matched_steps: matched, steps: outcome.steps, original_steps: original_steps,
                     detail: outcome.detail, exception: outcome.exception)
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
