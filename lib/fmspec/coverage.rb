# frozen_string_literal: true

module Fmspec
  # Model-Based Testing のカバレッジ（仕様書 §11.3）。`TestResult#coverage` が作る。
  #
  # テストが確実に通ったモデルの状態と遷移を、到達可能な状態と遷移と比べる。
  # 候補が1つに定まらない状態や、応答を説明できる遷移が1つに定まらないステップは数えない。
  # 部分観測や非決定性のあるモデルでは、実装が実際に通った数より少なく数えることがあるが、多く数えることはない。
  # モデルの状態と遷移を覆っても、実装の全経路を検査したことにはならない。
  class Coverage
    # 覆った数と、到達可能な数。
    Count = Struct.new(:covered, :reachable) do
      def ratio = reachable.zero? ? 1.0 : covered.fdiv(reachable)
      def to_s = format("%d/%d (%.1f%%)", covered, reachable, ratio * 100)
    end

    # 操作ごとの、テストで実行したステップ数と、その操作の遷移のカバレッジ。
    Action = Struct.new(:steps, :transitions)

    # テストのケースから、確実に通った状態と遷移を集める。
    class Collector
      attr_reader :ambiguous_steps, :steps

      def initialize
        @states = Set.new
        @transitions = Set.new
        @ambiguous_steps = 0
        @steps = Hash.new(0)
      end

      # 初期観測の照合。
      def initial(covered)
        @states << covered["state"] if covered && covered["state"]
      end

      # command の実行と照合。
      def step(action, covered)
        @steps[action] += 1
        @states << covered["state"] if covered && covered["state"]
        if covered && covered["transition"]
          @transitions << covered["transition"]
        else
          @ambiguous_steps += 1
        end
      end

      # エンジンに渡す、状態と遷移の符号の列。
      def seen = { "states" => @states.to_a, "transitions" => @transitions.to_a }
    end

    attr_reader :states, :transitions, :actions, :uncovered, :uncovered_count, :ambiguous_steps

    def initialize(body, collector)
      @complete = body["complete"]
      @states = Count.new(body["states"]["covered"], body["states"]["reachable"])
      @transitions = Count.new(body["transitions"]["covered"], body["transitions"]["reachable"])
      @actions = body["actions"].to_h do |a|
        name = a["name"].to_sym
        [name, Action.new(collector.steps[name], Count.new(a["covered"], a["reachable"]))]
      end
      @uncovered = body["uncovered"]
      @uncovered_count = body["uncovered_count"]
      @ambiguous_steps = collector.ambiguous_steps
    end

    # 到達可能な状態と遷移をすべて数えたか。偽なら、分母は到達可能な状態と遷移の一部である。
    def complete? = @complete

    def to_s
      lines = ["Coverage:"]
      lines << "  states: #{states}"
      lines << "  transitions: #{transitions}"
      actions.each do |name, a|
        lines << "  #{name}: #{a.steps} steps, transitions #{a.transitions}"
      end
      if ambiguous_steps.positive?
        lines << "  遷移が1つに定まらなかったステップ: #{ambiguous_steps}（カバレッジに数えていません）"
      end
      unless uncovered.empty?
        lines << "  覆っていない遷移（#{uncovered_count} 件#{uncovered_count > uncovered.length ? "、先頭 #{uncovered.length} 件" : ''}）:"
        uncovered.each do |u|
          args = u["args"].merge(u["choices"]).map { |k, v| "#{k}: #{JSON.generate(v)}" }.join(", ")
          lines << "    #{u['action']}(#{args}) from #{JSON.generate(u['state'])}"
        end
      end
      lines << "  探索を打ち切ったので、分母は到達可能な状態と遷移の一部です" unless complete?
      lines.join("\n") + "\n"
    end

    def inspect = "#<Fmspec::Coverage states #{states}, transitions #{transitions}>"
  end
end
