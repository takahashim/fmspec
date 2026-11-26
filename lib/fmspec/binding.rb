# frozen_string_literal: true

module Fmspec
  # 仕様と実装の結合（仕様書 §11.1）。操作ごとのハンドラと、観測対象ごとのアクセサを持つ。
  #
  #   binding = Tickets.bind do
  #     setup { BoxOffice.new(capacity: 3) }
  #     command(:purchase) { |office, quantity:| office.sell(quantity) }
  #     command(:cancel, method: :refund)
  #     observe(:sold) { |office| office.sold }
  #   end
  #
  # command と observe のブロックは実装を操作する普通の Ruby で、仕様の記号式とは別のものである。
  class Binding
    Handler = Struct.new(:name, :callable, :source, :inject)

    attr_reader :model, :commands, :observers

    def initialize(model, &block)
      raise BuildError, "bind にはブロックが必要です" unless block

      @model = model
      @setup = nil
      @teardown = nil
      @commands = {}
      @observers = {}
      instance_eval(&block)
      validate!
      freeze
    end

    # 各テストケースで、新しい実装のコンテキストを返す。
    def setup(&block)
      raise BuildError, "setup にはブロックが必要です" unless block
      raise BuildError, "setup は1つだけ書けます" if @setup

      @setup = block
    end

    # 各テストケースの終わりに、失敗したときも呼ばれる。
    def teardown(&block)
      raise BuildError, "teardown にはブロックが必要です" unless block
      raise BuildError, "teardown は1つだけ書けます" if @teardown

      @teardown = block
    end

    # 操作のハンドラ。ブロックは実装のコンテキストと、操作の引数（キーワード）を受け取る。
    # 操作が出力を宣言していれば、ブロックの戻り値を仕様の出力と比べる。
    # `command :cancel, method: :refund` は、コンテキストの refund を引数付きで呼ぶ。
    #
    # `inject:` は障害注入である（仕様書 §12.3）。名前を挙げた内部選択は、実装が決めるのではなく、
    # テストが値を選んでブロックにキーワードで渡す。ブロックは、その値のとおりに振る舞うよう
    # fake や注入点に指示してから、実装を呼ぶ。
    def command(name, method: nil, inject: [], &block)
      register(@commands, name, "command", method, block) do |m|
        ->(context, **args) { args.empty? ? context.public_send(m) : context.public_send(m, **args) }
      end
      @commands[name.to_sym].inject = Array(inject).map(&:to_sym).freeze
    end

    # 状態変数の観測。ブロックは実装のコンテキストを受け取り、仕様上の値を返す。
    def observe(name, method: nil, &block)
      register(@observers, name, "observe", method, block) { |m| ->(context) { context.public_send(m) } }
    end

    def setup_block = @setup
    def teardown_block = @teardown

    private

    def register(table, name, what, method, block)
      name = name.to_sym
      raise BuildError, "#{what} #{name} の登録が重複しています" if table.key?(name)
      raise BuildError, "#{what} #{name} には、ブロックか method: のどちらか一方を渡します" unless method.nil? ^ block.nil?

      location = caller_locations(2, 1)&.first
      source = block ? block.source_location&.join(":") : location && "#{location.path}:#{location.lineno}"
      table[name] = Handler.new(name, block || yield(method.to_sym), source, [].freeze)
    end

    # 登録を、実行の前に仕様と照合する。
    def validate!
      raise BuildError, "bind には setup が必要です" unless @setup

      ir = @model.to_ir
      actions = ir["actions"].to_h { |a| [a["name"].to_sym, a] }
      states = ir["states"].map { |s| s["name"].to_sym }
      missing = actions.keys - @commands.keys
      raise BuildError, "command が登録されていない操作があります: #{missing.join(', ')}" unless missing.empty?

      extra = @commands.keys - actions.keys
      raise BuildError, "仕様にない操作の command があります: #{extra.join(', ')}" unless extra.empty?

      unknown = @observers.keys - states
      raise BuildError, "仕様にない状態変数の observe があります: #{unknown.join(', ')}" unless unknown.empty?

      @commands.each_value { |handler| check_keywords(handler, actions[handler.name]) }
    end

    # command のブロックのキーワード引数が、操作の公開引数と合うことを確かめる。
    def check_keywords(handler, action)
      choices = action["choices"].map { |c| c["name"].to_sym }
      unknown = handler.inject - choices
      unless unknown.empty?
        raise BuildError, "command #{handler.name} の inject に、操作にない内部選択があります: #{unknown.join(', ')}"
      end
      return unless handler.callable.is_a?(Proc) && !handler.callable.lambda?

      params = action["params"].map { |p| p["name"].to_sym } + handler.inject
      kinds = handler.callable.parameters
      return if kinds.any? { |kind, _| kind == :keyrest }

      keywords = kinds.select { |kind, _| %i[key keyreq].include?(kind) }.map(&:last)
      unexpected = kinds.select { |kind, _| kind == :keyreq }.map(&:last) - params
      unhandled = params - keywords
      return if unexpected.empty? && unhandled.empty?

      raise BuildError, "command #{handler.name} のブロックのキーワード引数（#{keywords.join(', ')}）が、" \
                        "操作の引数と注入する選択（#{params.join(', ')}）と合いません"
    end
  end
end
