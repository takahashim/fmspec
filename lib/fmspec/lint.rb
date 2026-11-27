# frozen_string_literal: true

require "prism"

module Fmspec
  # 記号ブロックの構文検査（仕様書 §4.1）。
  #
  # 記号ブロック（action、invariant、terminal、ensures などのブロック）は、仕様の構築時に一度だけ
  # 実行して式を組み立てる。その中で Ruby の `if` や `&&` や `==` を記号式に使うと、Ruby は構築時の
  # 値で分岐や比較をしてしまい、書いたつもりの条件が式に残らない。そこで、ブロックのソースを
  # Prism で読み、これらの構文があれば拒否する。
  #
  # 検査はブロックの中の構文すべてが対象で、記号式に使っているかどうかは区別しない。
  # 静的な分岐や繰り返しは、記号ブロックの外に書く。ソースを読めないブロックは検査できないので拒否する。
  module Lint
    NODES = {
      Prism::IfNode => "if と条件演算子は使えません。条件式は ite(条件, 真の値, 偽の値) で書きます",
      Prism::UnlessNode => "unless は使えません。条件式は ite で書きます",
      Prism::AndNode => "&& と and は使えません。& を使います（両辺を括弧で囲みます）",
      Prism::OrNode => "|| と or は使えません。| を使います（両辺を括弧で囲みます）",
      Prism::CaseNode => "case は使えません。条件式は ite で書きます",
      Prism::CaseMatchNode => "case/in は使えません。条件式は ite で書きます",
      Prism::WhileNode => "while は使えません",
      Prism::UntilNode => "until は使えません"
    }.freeze

    CALLS = {
      :== => "== は使えません。eq を使います",
      :!= => "!= は使えません。ne を使います",
      :! => "! と not は使えません。not_ を使います"
    }.freeze

    # Ruby の Enumerable で、ブロックの結果を Ruby の真偽値として使うメソッド。記号式は Ruby の値としてつねに真なので、
    # ブロックが記号式を返すと、書いたつもりの条件は式に残らない。記号式にはこれらのメソッドはない。
    TRUTHY_BLOCKS = %i[select filter reject find detect find_all find_index count partition filter_map
                       take_while drop_while min_by max_by sort_by group_by chunk_while slice_when].freeze

    # 結果が Ruby の Array や Range になる式。記号式の all? と any? と区別する。
    # 記号式にもあるメソッド（Map の keys など）は、どちらか決められないので含めない。
    RUBY_COLLECTIONS = %i[map flat_map collect select filter reject to_a to_set each_with_index each_slice each_cons
                          zip product combination permutation repeated_permutation values sort uniq].freeze

    @parsed = {}

    module_function

    # ブロックを検査する。使えない構文があれば BuildError。
    def check!(block, what)
      file, line = block.source_location
      unless file && File.file?(file)
        raise BuildError, "#{what}: ブロックのソースを読めないので、構文を検査できません（#{file.inspect}）"
      end

      blocks = blocks_at(file, line)
      raise BuildError, "#{what}: #{file}:#{line} にブロックが見つかりません" if blocks.empty?

      # 同じ行で始まるブロックが複数あれば、どれが対象かを決めずに、すべて検査する。
      blocks.each { |node| scan(node, file, what) }
    end

    def blocks_at(file, line)
      found = []
      walk(parse(file)) do |node|
        found << node if (node.is_a?(Prism::BlockNode) || node.is_a?(Prism::LambdaNode)) && node.location.start_line == line
      end
      found
    end

    def parse(file)
      mtime = File.mtime(file)
      cached = @parsed[file]
      return cached[1] if cached && cached[0] == mtime

      result = Prism.parse_file(file)
      @parsed[file] = [mtime, result.value]
      result.value
    end

    def scan(block, file, what)
      walk(block) do |node|
        message = NODES[node.class]
        message ||= CALLS[node.name] || truthiness(node) if node.is_a?(Prism::CallNode)
        next unless message

        raise BuildError, "#{what}: #{file}:#{node.location.start_line}: 記号ブロックの中で#{message}"
      end
    end

    # 記号式を Ruby の真偽値として読むメソッドの呼び出し。
    def truthiness(call)
      name = call.name
      # none? は Option の記号式にもあるので、記号式にない one? だけを拒否する。
      if name == :one?
        "one? は使えません。Ruby の Enumerable は記号式をつねに真として扱います。forall、exists、all、any を使います"
      elsif TRUTHY_BLOCKS.include?(name) && call.block
        "ブロック付きの #{name} は使えません。Ruby の Enumerable はブロックの結果をつねに真として扱います。" \
          "集合を記号ブロックの外で求めるか、forall、exists を使います"
      elsif %i[all? any?].include?(name) && ruby_collection?(call.receiver)
        "Ruby の Array や Range の #{name} は使えません。記号式をつねに真として扱います。" \
          "all(*...)、any(*...)、forall、exists を使います"
      elsif %i[include? member? key? has_key?].include?(name) && ruby_collection?(call.receiver)
        "Ruby の Array、Hash、Set、Range の #{name} は使えません。記号式と要素を比べられません。" \
          "set_of(型).value(...) の include? や eq を使います"
      elsif name == :nil?
        "nil? は使えません。記号式にはつねに偽を返します。Option の式には none? を使います"
      elsif %i[eql? equal?].include?(name)
        "#{name} は使えません。記号式どうしの等しさは eq で書きます"
      end
    end

    # Ruby のリテラルの Array、Hash、Range、Set[...]、または Ruby の Enumerable を返す呼び出し。
    def ruby_collection?(node)
      node = node.body.body.last while node.is_a?(Prism::ParenthesesNode) && node.body.is_a?(Prism::StatementsNode)
      case node
      when Prism::ArrayNode, Prism::HashNode, Prism::RangeNode then true
      when Prism::CallNode
        RUBY_COLLECTIONS.include?(node.name) ||
          (node.name == :[] && node.receiver.is_a?(Prism::ConstantReadNode) && node.receiver.name == :Set)
      else false
      end
    end

    def walk(node, &visit)
      return unless node

      yield node
      node.compact_child_nodes.each { |child| walk(child, &visit) }
    end
  end
end
