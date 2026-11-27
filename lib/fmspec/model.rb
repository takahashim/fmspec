# frozen_string_literal: true

module Fmspec
  # 仕様。`Fmspec.define` が作る。型付きIRを持ち、検査はエンジン（native extension）が行う。
  class Model
    attr_reader :name
    # Ghost State として宣言した状態変数の名前。
    attr_reader :ghosts

    # 並行するプロセス。プロセス名から、インスタンスの数（:count）とステップの名前の配列（:steps）への Hash。
    attr_reader :processes

    def initialize(name, ir, ghosts: [], processes: {})
      @name = name
      @ir = Model.deep_freeze(ir)
      @ghosts = ghosts.dup.freeze
      @processes = Model.deep_freeze(processes.transform_values(&:dup))
      @native = nil
    end

    # 生成したIR（Hash）。エンジンに渡すものと同じ内容である。
    def to_ir = @ir

    def to_json(*) = JSON.generate(@ir)

    # モデルのdigest。トレースと証明書に記録される。
    def digest = describe.fetch("model_digest")

    # モデル検査（仕様書 §8）。到達できるすべての状態と有効な遷移を、幅優先探索で検査する。
    #
    #   max_states      保持する異なる状態の数の上限。超える場合は :inconclusive
    #   max_depth       深さ（初期状態からの遷移数）の上限。上限より深い状態が残る場合は :inconclusive
    #   max_time_ms     探索と証拠の検査の時間の上限（ミリ秒）。超える場合は :inconclusive
    #   max_check_cost  判定ゲートが証拠の検査にかける評価回数の上限。見積もりが超える場合は :inconclusive
    #   deadlock        非終端のデッドロックを検査する
    #   actions、invariants、contracts   対象の名前の配列。省略時はすべて
    #   certificate     真なら、受理された証明書を結果に含める
    def check(max_states: nil, max_depth: nil, max_time_ms: nil, max_check_cost: nil, certificate: false, **conditions)
      options = condition_options(conditions)
      options["max_states"] = max_states if max_states
      options["max_depth"] = max_depth if max_depth
      options["max_time_ms"] = max_time_ms if max_time_ms
      options["max_check_cost"] = max_check_cost if max_check_cost
      options["certificate"] = true if certificate
      result(native.check(JSON.generate(options)))
    end

    # ランダムシミュレーション（仕様書 §9）。成功は :sampled で、網羅性の主張はない。
    # seed を省略すると無作為に選び、結果に記録する。`max_time_ms` は check と同じ。
    def simulate(traces: 100, max_steps: 100, seed: nil, max_time_ms: nil, **conditions)
      options = condition_options(conditions)
      options.merge!("traces" => traces, "max_steps" => max_steps, "seed" => seed || Random.new_seed % (2**64))
      options["max_time_ms"] = max_time_ms if max_time_ms
      result(native.simulate(JSON.generate(options)))
    end

    # 証明書（Hash またはJSON文字列）を、指定の検査条件で検査する。`max_check_cost` と `max_time_ms` は check と同じ。
    def verify_certificate(certificate, max_check_cost: nil, max_time_ms: nil, **conditions)
      certificate = JSON.generate(certificate) unless certificate.is_a?(String)
      options = condition_options(conditions)
      options["max_check_cost"] = max_check_cost if max_check_cost
      options["max_time_ms"] = max_time_ms if max_time_ms
      result(native.verify_certificate(certificate, JSON.generate(options)))
    end

    # トレース（Trace、Hash、またはJSON文字列）を、記録された検査条件で再生する。
    def replay(trace)
      trace = trace.to_h if trace.is_a?(Trace)
      trace = JSON.generate(trace) unless trace.is_a?(String)
      result(native.replay(trace))
    end

    # モデル違反のトレースを、同じ違反を保ったまま短くする（仕様書 §10）。結果は局所最小である。
    def shrink(trace, attempts: nil)
      trace = trace.to_h if trace.is_a?(Trace)
      trace = JSON.generate(trace) unless trace.is_a?(String)
      result(native.shrink(trace, JSON.generate(attempts ? { "attempts" => attempts } : {})))
    end

    # 実装との結合を宣言する（仕様書 §11.1）。ブロックの中の語彙は Fmspec::Binding にある。
    def bind(&block) = Binding.new(self, &block)

    # Model-Based Testing（仕様書 §11）。仕様から操作列を生成して実装に適用し、戻り値と観測を照合する。
    #
    #   cases    テストケースの数
    #   steps    1ケースの最大ステップ数
    #   seed     省略すると無作為に選び、結果に記録する
    #   replay   操作列（`TestResult#inputs`）か、モデル検査のトレース（`Result#trace`）。
    #            指定すると、生成せずにその操作列を1回だけ再実行する。並行するプロセスでは、反例のスケジュールの再現になる
    #   paths    操作列の配列。指定すると、生成せずに各操作列を1ケースとして再実行する。
    #            true なら `test_paths` で作る（steps が1経路の最大ステップ数）
    #   shrink   失敗した操作列を縮小する
    #   actions  対象の操作の名前の配列。省略時はすべて
    #   max_candidates  候補状態の数の上限。超える場合は :inconclusive
    #
    # 結果の `coverage` で、テストが確実に通ったモデルの状態と遷移の割合を確かめられる。
    def test(binding, cases: 100, steps: 20, seed: nil, replay: nil, paths: nil, shrink: true, shrink_runs: 200,
             actions: nil, max_candidates: nil)
      raise ArgumentError, "replay と paths は同時に指定できません" if replay && paths

      run = test_run(binding, cases: cases, steps: steps, seed: seed, shrink: shrink, shrink_runs: shrink_runs,
                              actions: actions, max_candidates: max_candidates)
      return run.replay(replay) if replay
      return run.run_paths(paths == true ? run.paths(max_steps: steps, max_states: nil) : paths) if paths

      run.run
    end

    # テスト経路を作る（仕様書 §11.3）。到達可能な状態と入力の組を覆う操作列の配列を返す。
    # 各操作列は `Model#test(binding, paths: ...)` で再実行できる。
    #
    #   max_steps   1経路の最大ステップ数
    #   max_states  到達可能な状態の探索の、状態数の上限
    #   actions     対象の操作の名前の配列。省略時はすべて
    #
    # binding が注入する内部選択は入力に含める。注入しない内部選択がある操作では、モデルが最初に列挙した
    # 遷移をたどる前提で経路を作るので、実装が別の遷移を選ぶと、その経路は :inconclusive（invalid_input）になる。
    def test_paths(binding, max_steps: 20, max_states: nil, actions: nil)
      raise ArgumentError, "max_steps は1以上の整数です" unless max_steps.is_a?(Integer) && max_steps >= 1

      test_run(binding, actions: actions).paths(max_steps: max_steps, max_states: max_states)
    end

    def inspect = "#<Fmspec::Model #{name}>"

    def self.deep_freeze(value)
      case value
      when Hash then value.each_value { |v| deep_freeze(v) }
      when Array then value.each { |v| deep_freeze(v) }
      end
      value.freeze
    end

    private

    # エンジンが検証したモデル。最初に使うときに読み込む。
    def native
      @native ||= begin
        loaded = Native::Model.load(to_json)
        raise InvalidModelError, JSON.parse(loaded).fetch("message") if loaded.is_a?(String)

        loaded
      end
    end

    def describe = JSON.parse(native.describe)

    def test_run(binding, cases: 0, steps: 0, seed: nil, shrink: true, shrink_runs: 200, actions: nil, max_candidates: nil)
      raise ArgumentError, "この仕様の binding ではありません" unless binding.is_a?(Binding) && binding.model.equal?(self)
      raise ArgumentError, "cases と steps は0以上の整数です" unless [cases, steps].all? { |n| n.is_a?(Integer) && n >= 0 }

      options = {}
      options["actions"] = Array(actions).map(&:to_s) if actions
      options["max_candidates"] = max_candidates if max_candidates
      TestRun.new(self, native, binding, cases: cases, steps: steps, seed: seed || Random.new_seed % (2**64),
                                         shrink: shrink, shrink_runs: shrink_runs, options: options)
    end

    def condition_options(conditions)
      unknown = conditions.keys - %i[deadlock actions invariants contracts]
      raise ArgumentError, "未知のオプション: #{unknown.join(', ')}" unless unknown.empty?

      options = {}
      options["deadlock"] = conditions[:deadlock] ? true : false if conditions.key?(:deadlock)
      %i[actions invariants contracts].each do |key|
        options[key.to_s] = Array(conditions[key]).map(&:to_s) if conditions[key]
      end
      options
    end

    def result(json)
      body = JSON.parse(json)
      raise ArgumentError, body["message"] if body["status"] == "usage_error"

      Result.new(body)
    end
  end
end
