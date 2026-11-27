# frozen_string_literal: true

module Fmspec
  # トレース。初期状態からの操作列と、各ステップの出力と状態、末尾で起きる事象の主張を持つ。
  class Trace
    Step = Struct.new(:action, :args, :choices, :output, :state)

    def initialize(raw)
      @raw = raw
    end

    # 初期状態。状態変数名から値への Hash。
    def initial = @raw["initial"]

    def steps
      @steps ||= @raw["steps"].map do |s|
        output = s["output"].key?("value") ? s["output"]["value"] : nil
        Step.new(s["action"].to_sym, s["args"], s["choices"], output, s["state"]).freeze
      end.freeze
    end

    def length = @raw["steps"].length

    # 各ステップ後の状態。初期状態は含まない。
    def states = steps.map(&:state)

    def seed = @raw["seed"]

    # エンジンのトレース形式（docs/ir.md）。`Model#replay` に渡せる。
    def to_h = @raw
    def to_json(*) = JSON.generate(@raw)
  end

  # 検査の結果（仕様書 §8.3）。
  #
  # :verified、:violated、:error は、エンジンの判定ゲートが証拠を検査してから返した判定である。
  # :sampled はサンプルの検査を完了しただけで、網羅性の主張はない。
  class Result
    STATUSES = %i[verified violated error inconclusive sampled rejected internal_error].freeze

    def initialize(raw)
      @raw = Model.deep_freeze(raw)
    end

    def status = @raw["status"].to_sym

    STATUSES.each do |name|
      define_method(:"#{name}?") { status == name }
    end

    # 違反した性質、または評価エラーの箇所。:violated と :error のとき。
    def property = @raw["property"]

    # 違反または評価エラーに至るトレース。:violated と :error のとき。
    def trace = @raw["trace"] && Trace.new(@raw["trace"])

    # 受理された証明書。`check(certificate: true)` で :verified のとき。
    def certificate = @raw["certificate"]

    # :inconclusive の理由。:max_states、:max_depth、:max_time_ms、:max_check_cost、:interrupted のいずれか。
    # Ruby からの割り込みはふつう例外として伝わるので、:interrupted になるのは、
    # 割り込みが例外を投げずに終わった場合（シグナルのトラップが例外を投げずに戻った場合など）に限る。
    def reason = @raw["reason"]&.to_sym

    # 探索器の報告。検査済みの値ではない。
    def search = @raw["search"]
    def simulation = @raw["simulation"]
    def visited_states = search&.fetch("visited_states")
    def seed = simulation&.fetch("seed")

    # 判定ゲートが証拠を拒否した理由。:rejected のときと、探索器の証拠を拒否した :internal_error のとき。
    def rejected = @raw["rejected"]

    # 探索器の内部の不整合の内容。証拠を生成できなかった :internal_error のとき。
    # kind（"successors"）、action、state（状態型に従うときだけ）、encoded_state、message を持つ。
    def inconsistency = @raw["inconsistency"]

    def to_h = @raw

    # 人間向けの報告。
    def to_s = Native.format(JSON.generate(@raw))

    def inspect = "#<Fmspec::Result #{status}>"
  end
end
