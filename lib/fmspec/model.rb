# frozen_string_literal: true

module Fmspec
  # 仕様。`Fmspec.define` が作る。型付きIRを持ち、検査はエンジン（native extension）が行う。
  class Model
    attr_reader :name
    # Ghost State として宣言した状態変数の名前。
    attr_reader :ghosts

    # 並行するプロセス。プロセス名から、インスタンスの数（:count）とステップの名前の配列（:steps）への Hash。
    attr_reader :processes

    # `with` で上書きした定数の値。定数の名前（Symbol）から値への Hash。
    attr_reader :overrides

    def initialize(name, ir, ghosts: [], processes: {}, definition: nil, overrides: {})
      @name = name
      @definition = definition
      @overrides = overrides.dup.freeze
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
    #   symmetry        偽なら、宣言した対称性による削減を使わない（既定は、宣言があれば使う）
    def check(max_states: nil, max_depth: nil, max_time_ms: nil, max_check_cost: nil, certificate: false, symmetry: nil,
              **conditions)
      options = condition_options(conditions)
      options["symmetry"] = symmetry unless symmetry.nil?
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
    #
    #   allow_other_model  真なら、model_digest が違う（別のモデルに対する）証明書も、このモデルの名前と型で読んで検査する。
    #                      偽（既定）なら、別のモデルに対する証明書は :rejected（読めない証拠）になる
    def verify_certificate(certificate, max_check_cost: nil, max_time_ms: nil, allow_other_model: false, **conditions)
      certificate = JSON.generate(certificate) unless certificate.is_a?(String)
      options = condition_options(conditions)
      options["max_check_cost"] = max_check_cost if max_check_cost
      options["max_time_ms"] = max_time_ms if max_time_ms
      options["allow_other_model"] = true if allow_other_model
      result(native.verify_certificate(certificate, JSON.generate(options)))
    end

    # トレース（Trace、Hash、またはJSON文字列）を、記録された検査条件で再生する。
    # `max_check_cost` と `allow_other_model` は verify_certificate と同じ。
    # 判定ゲートはトレースを区切らずに検査するので、時間の上限は受け付けず、割り込みは検査を終えてから伝わる。
    def replay(trace, max_check_cost: nil, allow_other_model: false)
      options = {}
      options["max_check_cost"] = max_check_cost if max_check_cost
      options["allow_other_model"] = true if allow_other_model
      result(native.replay(trace_json(trace), JSON.generate(options)))
    end

    # モデル違反のトレースを、同じ違反を保ったまま短くする（仕様書 §10）。結果は局所最小である。
    # `attempts` は試す候補の数の上限、`max_time_ms` は縮小の時間の上限で、達したら縮小を打ち切り、
    # それまでに判定ゲートが受理したトレースを返す（`Result#shrink` に打ち切ったことを記録する）。
    # `max_check_cost` は元のトレースの検査の上限で、`allow_other_model` は verify_certificate と同じ。
    def shrink(trace, attempts: nil, max_time_ms: nil, max_check_cost: nil, allow_other_model: false)
      options = {}
      options["attempts"] = attempts if attempts
      options["max_time_ms"] = max_time_ms if max_time_ms
      options["max_check_cost"] = max_check_cost if max_check_cost
      options["allow_other_model"] = true if allow_other_model
      result(native.shrink(trace_json(trace), JSON.generate(options)))
    end

    # 定数を上書きして、仕様を作り直す。`Fmspec.define` のブロックをもう一度実行する。
    # これまでの上書きに `overrides` を重ねる。値の型は、宣言した定数の型に合わなければならない。
    #
    #   Tickets.with(capacity: 4).check.verified?
    #
    # 結果は、その値のモデルについての判定である。定数のほかの値については何も主張しない。
    def with(**overrides)
      raise BuildError, "#{name} は Fmspec.define で定義した仕様ではないので、定数を上書きできません" unless @definition

      @definition.call(@overrides.merge(overrides.transform_keys(&:to_sym)))
    end

    # 定数の値の候補の直積について、組み合わせごとに `with` で作り直して検査する。
    # 候補は範囲か配列で書く。組み合わせ（Hash）と結果の対の配列を返す。順は候補の直積の順（最初の定数が最も遅く変わる）である。
    # ブロックを渡すと、作り直したモデルを受け取り、その戻り値を結果にする。既定は `check`。
    #
    #   Tickets.sweep(capacity: 2..4).each { |values, result| puts "#{values} #{result.status}" }
    #   Tickets.sweep(capacity: 2..4) { |m| m.check(deadlock: true) }
    #
    # 各結果は、その組み合わせのモデルについての判定であり、定数一般についての主張ではない。
    def sweep(**domains)
      raise ArgumentError, "sweep には、定数の名前と値の候補を1つ以上渡します" if domains.empty?

      names = domains.keys.map(&:to_sym)
      candidates = domains.map { |key, domain| sweep_candidates(key, domain) }
      candidates.first.product(*candidates.drop(1)).map do |combination|
        values = names.zip(combination).to_h
        model = with(**values)
        [values, block_given? ? yield(model) : model.check]
      end
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

    def sweep_candidates(name, domain)
      unless domain.is_a?(Range) || domain.is_a?(Array)
        raise ArgumentError, "定数 #{name} の候補は、範囲か配列で書きます: #{domain.inspect}"
      end
      raise ArgumentError, "定数 #{name} の候補の範囲に終わりがありません" if domain.is_a?(Range) && domain.end.nil?

      values = domain.to_a
      raise ArgumentError, "定数 #{name} の候補が空です" if values.empty?

      values
    end

    # エンジンが検証したモデル。最初に使うときに読み込む。
    def native
      @native ||= begin
        loaded = Native::Model.load(to_json)
        raise InvalidModelError, JSON.parse(loaded).fetch("message") if loaded.is_a?(String)

        loaded
      end
    end

    def describe = JSON.parse(native.describe)

    def trace_json(trace)
      trace = trace.to_h if trace.is_a?(Trace)
      trace.is_a?(String) ? trace : JSON.generate(trace)
    end

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
