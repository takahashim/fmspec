# frozen_string_literal: true

module Fmspec
  # 仕様。`Fmspec.define` が作る。型付きIRを持ち、検査はエンジン（native extension）が行う。
  class Model
    attr_reader :name

    def initialize(name, ir)
      @name = name
      @ir = Model.deep_freeze(ir)
      @native = nil
    end

    # 生成したIR（Hash）。エンジンに渡すものと同じ内容である。
    def to_ir = @ir

    def to_json(*) = JSON.generate(@ir)

    # モデルのdigest。トレースと証明書に記録される。
    def digest = describe.fetch("model_digest")

    # モデル検査（仕様書 §8）。到達できるすべての状態と有効な遷移を、幅優先探索で検査する。
    #
    #   max_states   保持する異なる状態の数の上限。超える場合は :inconclusive
    #   deadlock     非終端のデッドロックを検査する
    #   actions、invariants、contracts   対象の名前の配列。省略時はすべて
    #   certificate  真なら、受理された証明書を結果に含める
    def check(max_states: nil, certificate: false, **conditions)
      options = condition_options(conditions)
      options["max_states"] = max_states if max_states
      options["certificate"] = true if certificate
      result(native.check(JSON.generate(options)))
    end

    # ランダムシミュレーション（仕様書 §9）。成功は :sampled で、網羅性の主張はない。
    # seed を省略すると無作為に選び、結果に記録する。
    def simulate(traces: 100, max_steps: 100, seed: nil, **conditions)
      options = condition_options(conditions)
      options.merge!("traces" => traces, "max_steps" => max_steps, "seed" => seed || Random.new_seed % (2**64))
      result(native.simulate(JSON.generate(options)))
    end

    # 証明書（Hash またはJSON文字列）を、指定の検査条件で検査する。
    def verify_certificate(certificate, **conditions)
      certificate = JSON.generate(certificate) unless certificate.is_a?(String)
      result(native.verify_certificate(certificate, JSON.generate(condition_options(conditions))))
    end

    # トレース（Trace、Hash、またはJSON文字列）を、記録された検査条件で再生する。
    def replay(trace)
      trace = trace.to_h if trace.is_a?(Trace)
      trace = JSON.generate(trace) unless trace.is_a?(String)
      result(native.replay(trace))
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
