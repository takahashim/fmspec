# frozen_string_literal: true

module Fmspec
  # 詳細化の検査（docs/plans/refinement_symmetry_constants.md の2）。`Fmspec.refinement` が作る。
  #
  # 具体モデルの状態から抽象モデルの状態への写像を、抽象モデルの状態変数ごとに、具体モデルの状態の上の式で書く。
  # 検査は、具体モデルの初期状態が抽象モデルの初期状態に写り、具体モデルの到達可能な状態からの有効な遷移が、
  # 抽象モデルの遷移か、写した状態の変わらないステップに写ることを確かめる。活性と公平性の保存は扱わない。
  #
  #   CounterRefinesAtomic = Fmspec.refinement(:counter_refines_atomic, concrete: Counter, abstract: Atomic) do
  #     map(:count) { |s| s.count }
  #   end
  #   CounterRefinesAtomic.check.refines?
  class Refinement
    include Functions

    # 写像のブロックの中の語彙。
    class Builder
      include Functions

      def initialize(refinement)
        @refinement = refinement
      end

      # 抽象モデルの状態変数 `name` の写像。ブロックは具体モデルの記号的な状態を受け取る。
      def map(name, &block) = @refinement.add_map(name, caller_locations(1, 1), &block)
    end

    attr_reader :name, :concrete, :abstract

    def initialize(name, concrete, abstract)
      { concrete: concrete, abstract: abstract }.each do |key, model|
        unless model.is_a?(Model)
          raise BuildError, "Fmspec.refinement の #{key} は Fmspec::Model ではありません: #{model.inspect}"
        end
      end
      @name = name.to_sym
      @concrete = concrete
      @abstract = abstract
      @enums = {}
      [concrete, abstract].each { |m| merge_enums(m.to_ir) }
      @concrete_types = concrete.to_ir["states"].to_h { |s| [s["name"], Types.from_ir(s["type"], @enums)] }
      @abstract_types = abstract.to_ir["states"].to_h { |s| [s["name"], Types.from_ir(s["type"], @enums)] }
      @maps = {}
    end

    def add_map(name, locations, &block)
      name = name.to_s
      raise BuildError, "写像 #{name} にはブロックが必要です" unless block

      type = @abstract_types[name]
      raise BuildError, "抽象モデル #{@abstract.name} に状態変数 #{name} はありません" unless type
      raise BuildError, "状態変数 #{name} の写像は定義済みです" if @maps.key?(name)

      Lint.check!(block, "写像 #{name}")
      value = instance_exec(StateRef.new(self, "var"), &block)
      expr = Expr.lift(value, type.kind, enums: declared_enums).expect(type.kind, "写像 #{name}")
      @maps[name] = { "state" => name, "expr" => expr.node, "source" => source_of(locations) }
      nil
    end

    # 写像を書き終えたことを確かめる。
    def finish!
      missing = @abstract_types.keys - @maps.keys
      raise BuildError, "抽象モデルの状態変数 #{missing.join(', ')} の写像がありません" unless missing.empty?

      @ir = Model.deep_freeze(
        {
          "ir_version" => 1,
          "name" => @name.to_s,
          "concrete" => @concrete.to_ir,
          "abstract" => @abstract.to_ir,
          "mapping" => @abstract_types.keys.map { |n| @maps[n].except("source") }
        }
      )
      self
    end

    # 具体モデルの状態変数の式。
    def reference(name, ref)
      name = name.to_s
      index = @concrete.to_ir["states"].index { |s| s["name"] == name }
      raise BuildError, "具体モデル #{@concrete.name} に状態変数 #{name} はありません" unless index

      Expr.new({ ref => index }, @concrete_types.fetch(name).kind)
    end

    # 詳細化の検査の文書（docs/ir.md の「詳細化」）。
    def to_ir = @ir
    def to_json(*) = JSON.generate(@ir)

    # 詳細化の検査。具体モデルを幅優先で探索し、判定ゲートが証拠を検査してから結果を返す。
    #
    #   max_states  保持する異なる状態の数の上限。超える場合は :inconclusive
    #   actions     具体モデルの対象の操作の名前の配列。省略時はすべて
    #
    # 抽象モデルの操作は、すべてを照合に使う。具体モデルの不変条件と遷移契約は検査しない。
    def check(max_states: nil, actions: nil)
      options = {}
      options["max_states"] = max_states if max_states
      options["actions"] = actions.map(&:to_s) if actions
      raw = JSON.parse(Native.refine(to_json, JSON.generate(options)))
      raise InvalidModelError, raw.fetch("message") if raw["status"] == "invalid_model"
      raise ArgumentError, raw.fetch("message") if raw["status"] == "usage_error"

      RefinementResult.new(raw)
    end

    def inspect = "#<Fmspec::Refinement #{name}: #{@concrete.name} -> #{@abstract.name}>"

    private

    def declared_enums = @enums.values

    def merge_enums(ir)
      Array(ir["enums"]).each do |e|
        type = Types::Enum.new(e["name"].to_sym, e["variants"].map(&:to_sym))
        known = @enums[e["name"]]
        if known && known != type
          raise BuildError, "列挙型 #{e['name']} のラベルが、具体モデルと抽象モデルで違います。どちらかの名前を変えてください"
        end

        @enums[e["name"]] = type
      end
    end

    def source_of(locations)
      location = locations&.first
      location && { "file" => location.path, "line" => location.lineno }
    end
  end

  # 詳細化の検査の結果。
  #
  # :refines、:not_refines、:error は、エンジンの判定ゲートが証拠を検査してから返した判定である。
  class RefinementResult
    STATUSES = %i[refines not_refines error inconclusive internal_error].freeze

    def initialize(raw)
      @raw = Model.deep_freeze(raw)
    end

    def status = @raw["status"].to_sym

    STATUSES.each do |name|
      define_method(:"#{name}?") { status == name }
    end

    # 詳細化が破れた箇所（"violation" が "initial"、"step"）、または評価エラーの箇所。
    def property = @raw["property"]

    # 詳細化が破れる、または評価エラーに至る具体モデルのトレース。
    def trace = @raw["trace"] && Trace.new(@raw["trace"])

    # トレースの各状態を写した抽象モデルの状態。初期状態を含む。写像の評価が失敗した状態は nil。
    def abstract_states
      t = @raw["trace"]
      t && [t["initial_abstract"], *t["steps"].map { |s| s["abstract"] }]
    end

    # :inconclusive の理由。:max_states、:interrupted、:abstract_failed のいずれか。
    def reason = @raw["reason"]&.to_sym

    def search = @raw["search"]
    def visited_states = search&.fetch("visited_states")
    def rejected = @raw["rejected"]
    def to_h = @raw
    def to_s = Native.format(JSON.generate(@raw))
    def inspect = "#<Fmspec::RefinementResult #{status}>"
  end
end
