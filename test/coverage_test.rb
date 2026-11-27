# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# Model-Based Testing のカバレッジと、テスト経路の生成（仕様書 §11.3）。
class CoverageTest < Minitest::Test
  class BoxOffice
    attr_reader :sold

    def initialize(bug: nil)
      @sold = 0
      @bug = bug
    end

    def sell(quantity) = @sold += quantity

    def refund
      @sold -= @bug == :double_refund && @sold == 2 ? 2 : 1
    end
  end

  # 販売数 0..3 の4状態。遷移は purchase(1) が3本、purchase(2) が2本、cancel が3本の計8本。
  def tickets = @tickets ||= TestModels.tickets

  def office(bug = nil)
    tickets.bind do
      setup { BoxOffice.new(bug: bug) }
      command(:purchase) { |o, quantity:| o.sell(quantity) }
      command(:cancel, method: :refund)
      observe(:sold) { |o| o.sold }
    end
  end

  def test_coverage_counts_the_states_and_transitions_the_tests_went_through
    result = tickets.test(office, cases: 50, steps: 20, seed: 1)
    assert_equal :passed, result.status
    coverage = result.coverage
    assert coverage.complete?
    assert_equal [4, 4], coverage.states.to_a
    assert_equal [8, 8], coverage.transitions.to_a
    assert_equal 0, coverage.ambiguous_steps
    assert_equal [], coverage.uncovered
    assert_equal [[5, 5], [3, 3]], [coverage.actions[:purchase].transitions.to_a, coverage.actions[:cancel].transitions.to_a]
    assert_equal result.matched_steps, coverage.actions.values.sum(&:steps)
    assert_match(%r{^  transitions: 8/8 \(100\.0%\)$}, coverage.to_s)
  end

  def test_coverage_lists_transitions_the_tests_missed
    # 1ステップでは、初期状態からの遷移しか通らない。
    result = tickets.test(office, cases: 1, steps: 1, seed: 3)
    coverage = result.coverage
    assert_equal [2, 4], coverage.states.to_a
    assert_equal [1, 8], coverage.transitions.to_a
    assert_equal 7, coverage.uncovered_count
    assert(coverage.uncovered.all? { |u| %w[purchase cancel].include?(u["action"]) })
    assert_match(/覆っていない遷移（7 件）/, coverage.to_s)

    # 探索を打ち切ると、分母は到達可能な状態の一部になる。
    limited = result.coverage(max_states: 2)
    refute limited.complete?
    assert_equal 2, limited.states.reachable
  end

  # 内部選択で x が 0 か 1 になる。x を観測しなければ、どちらの遷移を通ったかは分からない。
  def coin
    Fmspec.define(:coin) do
      state :x, int(0..1), initial: 0
      state :flips, int(0..1), initial: 0
      action :flip do |s|
        guard s.flips.eq(0)
        heads = choose(:heads, bool)
        update x: ite(heads, 1, 0), flips: 1
      end
      action :spend do |s|
        guard s.x.eq(1)
        update x: 0
      end
    end
  end

  Coin = Struct.new(:x, :flips)

  def coin_binding(model, observe_x:, heads: true)
    model.bind do
      setup { Coin.new(0, 0) }
      command(:flip) do |c|
        c.x = heads ? 1 : 0
        c.flips = 1
      end
      command(:spend) { |c| c.x = 0 }
      observe(:flips, &:flips)
      observe(:x, &:x) if observe_x
    end
  end

  def test_steps_whose_transition_is_not_determined_are_not_counted
    model = coin
    hidden = model.test(coin_binding(model, observe_x: false), cases: 5, steps: 1, seed: 0)
    assert_equal :passed, hidden.status
    coverage = hidden.coverage
    assert_equal 5, coverage.ambiguous_steps
    assert_equal 0, coverage.transitions.covered
    # 候補が2つに分かれるので、遷移後の状態も数えない。初期状態だけを数える。
    assert_equal 1, coverage.states.covered
    assert_match(/遷移が1つに定まらなかったステップ: 5/, coverage.to_s)

    seen = model.test(coin_binding(model, observe_x: true), cases: 5, steps: 2, seed: 0)
    assert_equal :passed, seen.status
    assert_equal 0, seen.coverage.ambiguous_steps
    assert_equal 2, seen.coverage.transitions.covered
  end

  def test_test_paths_cover_every_state_and_input
    paths = tickets.test_paths(office, max_steps: 20)
    assert(paths.all? { |p| p.length <= 20 })
    result = tickets.test(office, paths: paths)
    assert_equal :passed, result.status
    assert_equal paths.length, result.cases
    assert_equal [8, 8], result.coverage.transitions.to_a

    # 経路の長さが足りなければ、届く範囲だけを覆う。
    short = tickets.test_paths(office, max_steps: 1)
    assert_equal [[[:purchase, { quantity: 1 }]], [[:purchase, { quantity: 2 }]]], short
    assert_equal :passed, tickets.test(office, paths: true, steps: 1).status
  end

  def test_test_paths_find_a_wrong_implementation
    result = tickets.test(office(:double_refund), paths: true, steps: 20)
    assert_equal :conformance_failure, result.status
    assert_equal :cancel, result.steps.last.action
    assert_equal ["sold"], result.detail["mismatch"]
  end

  def test_a_path_the_implementation_does_not_follow_is_inconclusive
    model = coin
    # 経路は、表が出て spend できる状態を目指す。実装が裏を出すと、spend は無効になる。
    paths = model.test_paths(coin_binding(model, observe_x: true))
    assert_includes paths, [[:flip, {}], [:spend, {}]]
    result = model.test(coin_binding(model, observe_x: true, heads: false), paths: paths)
    assert_equal :inconclusive, result.status
    assert_equal :invalid_input, result.reason

    # 内部選択を注入すれば、経路は選択の値を含み、実装はそれに従う。
    injected = model.bind do
      setup { Coin.new(0, 0) }
      command(:flip, inject: [:heads]) do |c, heads:|
        c.x = heads ? 1 : 0
        c.flips = 1
      end
      command(:spend) { |c| c.x = 0 }
      observe(:flips, &:flips)
      observe(:x, &:x)
    end
    paths = model.test_paths(injected)
    assert_includes paths, [[:flip, { heads: true }], [:spend, {}]]
    result = model.test(injected, paths: paths)
    assert_equal :passed, result.status
    assert_equal [3, 3], result.coverage.transitions.to_a
  end

  # 探索器の内部の不整合で集めきれなかったグラフは、カバレッジの分母やテスト経路に使わない。
  # 不整合は公開APIからは起こせないので、エンジンが返す形の結果で確かめる。
  def test_an_inconsistency_while_collecting_the_graph_is_an_internal_error
    body = { "status" => "internal_error", "model" => "tickets",
             "inconsistency" => { "kind" => "successors", "action" => "purchase", "encoded_state" => [9] },
             "message" => "探索器の内部の不整合です。fmspec の不具合です" }
    error = assert_raises(Fmspec::InternalError) { Fmspec::TestRun.graph_body(JSON.generate(body)) }
    assert_match(/探索器の内部の不整合です/, error.message)
    assert_match(/"encoded_state":\[9\]/, error.message)

    usage = { "status" => "usage_error", "message" => "max_steps は1以上の整数です" }
    assert_raises(ArgumentError) { Fmspec::TestRun.graph_body(JSON.generate(usage)) }
    assert_equal [], Fmspec::TestRun.graph_body(JSON.generate("status" => "ok", "paths" => []))["paths"]
  end
end
