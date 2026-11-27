# frozen_string_literal: true

$LOAD_PATH.unshift(File.expand_path("../lib", __dir__))
require "minitest/autorun"
require "json"
require "open3"
require "tmpdir"
require "fileutils"
require "fmspec/dsl"

# 第三者が書いた TLA+ の仕様（tlaplus/Examples）と、同じモデルを DSL で書いたものを比べる。
#
# TLC との比較テスト（reference/test/tlc_test.rb）は、fmspec の IR を変換した TLA+ を TLC で検査する。
# 変換も比較も同じ作者が書いたので、IR の意味を変換で取り違えると見つからない。
# このテストでは、TLA+ の側は他人が書いた仕様をそのまま使い（examples/tlaplus/vendor）、
# DSL の側は、その仕様を読んで書き写したもの（examples/tlaplus/models）を使う。
# DSL の状態変数は、TLA+ の状態変数と一対一に対応させてあるので、状態の数をそのまま比べられる。
#
# 仕様ごとに、次を比べる。
#
# - 判定。TLC が不変条件の違反を報告するなら、fmspec も対応する不変条件の違反を報告する
# - 反例の長さ。どちらも幅優先で最短の反例を返す
# - 違反で止まるまでに見つけた状態の数
# - 不変条件を外して最後まで探索したときの、到達できる状態の数。tlaplus/Examples の manifest.json の記録とも比べる
#
#   TLA2TOOLS   tla2tools.jar のパス（必須。なければ skip）
#   JAVA        java の実行ファイル（既定は java）
#   FMSPEC_BIN  比較する実行ファイル（既定は target/debug/fmspec）
class TlaplusExamplesTest < Minitest::Test
  ROOT = File.expand_path("..", __dir__)
  BIN = ENV.fetch("FMSPEC_BIN", File.join(ROOT, "target/debug/fmspec"))
  JAR = ENV.fetch("TLA2TOOLS", "")
  JAVA = ENV.fetch("JAVA", "java")
  DIR = File.join(ROOT, "examples/tlaplus")

  # module      TLA+ のモジュール
  # model       DSL のモデル（examples/tlaplus/models）
  # config      TLC の設定の、定数と仕様の部分
  # type_ok     型の不変条件。DSL では型で表すので、対応する不変条件はない
  # invariants  TLA+ の不変条件から DSL の不変条件へ。:deadlock は fmspec のデッドロック検査にあたる
  # deadlock    TLC のデッドロック検査の有無（元の設定と同じ）
  # expected    manifest.json の記録。:violated は safety failure、整数は最後まで探索したときの状態の数。
  #             nil なら記録と比べない（判定は success として扱う）
  EXAMPLES = {
    "DieHard" => { model: "die_hard", config: "SPECIFICATION Spec", type_ok: %w[TypeOK],
                   invariants: { "NotSolved" => "not_solved" }, deadlock: true, expected: :violated },
    "TCommit" => { model: "t_commit", config: "CONSTANTS RM = {r1, r2, r3}\nSPECIFICATION TCSpec",
                   type_ok: %w[TCTypeOK], invariants: { "TCConsistent" => "consistent" }, deadlock: false, expected: 34 },
    "TwoPhase" => { model: "two_phase", config: "CONSTANTS RM = {r1, r2, r3}\nSPECIFICATION TPSpec",
                    type_ok: %w[TPTypeOK], invariants: {}, deadlock: true, expected: 288 },
    "EWD840" => { model: "ewd840", config: "CONSTANTS N = 3\nSPECIFICATION Spec", type_ok: %w[TypeOK],
                  invariants: { "TerminationDetection" => "termination_detection", "Inv" => "inv" },
                  deadlock: false, expected: 302 },
    "MissionariesAndCannibals" => { model: "missionaries_and_cannibals",
                                    config: "CONSTANTS Missionaries = {m1, m2, m3}\nCannibals = {c1, c2, c3}\nINIT Init\nNEXT Next",
                                    type_ok: %w[TypeOK], invariants: { "Solution" => "solution" }, deadlock: true,
                                    expected: :violated },
    "DiningPhilosophers" => { model: "dining_philosophers", config: "CONSTANTS N = 5\nSPECIFICATION Spec",
                              type_ok: %w[TypeOK], invariants: { "NoDeadlock" => :deadlock }, deadlock: true,
                              expected: 58 },
    # PlusCal から翻訳された仕様。DSL では process で書く。pc はインスタンスごとのプログラムカウンタにあたる。
    "Simple" => { model: "simple", config: "CONSTANT N = 5\nSPECIFICATION Spec", type_ok: %w[TypeOK],
                  invariants: { "PCorrect" => "p_correct", "Inv" => "inv" }, deadlock: true, expected: 723 },
    "Lock" => { model: "lock", config: "SPECIFICATION Spec", type_ok: %w[TypeOK],
                invariants: { "LockInv" => "lock_inv" }, deadlock: true, expected: 12 },
    "Peterson" => { model: "peterson", config: "SPECIFICATION Spec", type_ok: %w[TypeOK],
                    invariants: { "Inv" => "inv" }, deadlock: true, expected: 42 },
    "DiningPhilosophersPCal" => { model: "dining_philosophers_pcal", config: "CONSTANT NP = 5\nSPECIFICATION Spec",
                                  type_ok: %w[TypeOK], invariants: { "ExclusiveAccess" => "exclusive_access" },
                                  deadlock: true, expected: 67 },
    # manifest.json の状態の数は、不変条件 Inv を満たすすべての状態から始める ISpec のものなので、比べない。
    "MCBakery" => { model: "bakery", config: "CONSTANTS N = 2\nMaxNat = 2\nNat <- NatOverride\nSPECIFICATION Spec",
                    type_ok: %w[TypeOK], invariants: { "MutualExclusion" => "mutual_exclusion" }, deadlock: false,
                    expected: nil }
  }.freeze

  def setup
    skip "環境変数 TLA2TOOLS に tla2tools.jar のパスを指定してください" unless File.file?(JAR)
    skip "#{BIN} がありません。先に cargo build を実行してください" unless File.executable?(BIN)
    @dir = Dir.mktmpdir("fmspec-tlaplus")
    Dir[File.join(DIR, "vendor/*/*.tla")].each { |f| FileUtils.cp(f, @dir) }
  end

  def teardown
    FileUtils.remove_entry(@dir) if @dir
  end

  # TLC の結果。違反した不変条件（デッドロックなら :deadlock）、反例の長さ、見つけた状態の数。
  def tlc(name, invariants:, deadlock:)
    example = EXAMPLES.fetch(name)
    cfg = "#{name}_#{invariants.length}.cfg"
    lines = [example[:config], "INVARIANTS #{(example[:type_ok] + invariants).join(' ')}"]
    lines << "CHECK_DEADLOCK FALSE" unless deadlock
    File.write(File.join(@dir, cfg), "#{lines.join("\n")}\n")
    tmp = File.join(@dir, "java-tmp-#{name}")
    FileUtils.mkdir_p(tmp)
    out, = Open3.capture2e(JAVA, "-XX:+UseSerialGC", "-Djava.io.tmpdir=#{tmp}", "-cp", JAR, "tlc2.TLC",
                           "-workers", "1", "-nowarning", "-metadir", File.join(@dir, "meta-#{name}"),
                           "-config", cfg, name, chdir: @dir)
    distinct = out[/(\d+) distinct states found/, 1] or flunk "TLC が状態の数を報告しない\n#{out}"
    violated = out[/Error: Invariant (\w+) is violated/, 1] || (out.include?("Error: Deadlock reached") ? :deadlock : nil)
    if violated.nil? && !out.include?("Model checking completed. No error has been found.")
      flunk "TLC が失敗した\n#{out}"
    end
    # 反例は「State 1: <Initial predicate>」から始まる状態の列である。
    length = violated && (out.scan(/^State \d+:/).length - 1)
    { violated: violated, length: length, states: Integer(distinct) }
  end

  # fmspec の結果。invariants は DSL の不変条件の名前（対象外のものは IR から除く）。
  # max_states は探索する状態の数の上限。DSL のモデルの誤りで状態の空間が膨らむと、探索が終わらないことがある。
  def fmspec(name, invariants:, deadlock:, max_states:)
    example = EXAMPLES.fetch(name)
    path = File.join(DIR, "models/#{example[:model]}.rb")
    ir = eval(File.read(path, encoding: Encoding::UTF_8), TOPLEVEL_BINDING, path).to_ir # rubocop:disable Security/Eval
    ir = ir.merge("invariants" => (ir["invariants"] || []).select { |i| invariants.include?(i["name"]) })
    model = File.join(@dir, "#{example[:model]}.json")
    File.write(model, JSON.generate(ir))
    args = [BIN, "check", model, "--json", "--max-states", max_states.to_s]
    args << "--deadlock" if deadlock
    out, = Open3.capture2(*args)
    r = JSON.parse(out)
    violated = case r["status"]
               when "verified" then nil
               when "violated" then r["property"]["violation"] == "deadlock" ? :deadlock : r["property"]["name"]
               when "inconclusive"
                 flunk "#{name}: fmspec の探索した状態が #{max_states} を超えた（TLC の状態の数と大きく違う）"
               else flunk "fmspec の結果が #{r['status']}\n#{out}"
               end
    { violated: violated, length: violated && r["trace"]["steps"].length, states: r["search"]["visited_states"] }
  end

  # fmspec に探索させる状態の数の上限。TLC が見つけた状態の数より十分大きくする。
  def limit(tlc) = (tlc[:states] * 10) + 100

  EXAMPLES.each do |name, example|
    define_method("test_#{example[:model]}") do
      mapping = example[:invariants]
      tla_invariants = mapping.keys
      dsl_invariants = mapping.values.reject { |v| v == :deadlock }
      deadlock = example[:deadlock] || mapping.value?(:deadlock)

      # すべての不変条件で検査する。
      t = tlc(name, invariants: tla_invariants, deadlock: example[:deadlock])
      f = fmspec(name, invariants: dsl_invariants, deadlock: deadlock, max_states: limit(t))
      expected_violation = t[:violated] && (t[:violated] == :deadlock ? :deadlock : mapping.fetch(t[:violated]))
      same = ->(want, got, what) { want.nil? ? assert_nil(got, what) : assert_equal(want, got, what) }
      same.(expected_violation, f[:violated], "#{name}: TLC #{t} fmspec #{f}")
      same.(t[:length], f[:length], "#{name}: 反例の長さ")
      assert_equal t[:states], f[:states], "#{name}: 見つけた状態の数"
      if example[:expected] == :violated
        refute_nil t[:violated], "#{name}: manifest.json では safety failure"
      else
        assert_nil t[:violated], "#{name}: manifest.json では success"
      end

      # 不変条件を外して、到達できる状態をすべて数える。
      t = tlc(name, invariants: [], deadlock: false)
      f = fmspec(name, invariants: [], deadlock: false, max_states: limit(t))
      assert_nil t[:violated]
      assert_nil f[:violated]
      assert_equal t[:states], f[:states], "#{name}: 到達できる状態の数"
      assert_equal example[:expected], t[:states], "#{name}: manifest.json の状態の数" if example[:expected].is_a?(Integer)
    end
  end
end
