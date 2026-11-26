# frozen_string_literal: true

# Nupur の写し（仕様書 §3.2）。
#
# Nupur は Makiri のバインディング層で、公開crateではない。Makiri の特定コミットの
# `nupur` と `nupur_sys` のソースとマニフェストを vendor/nupur に写して使う。
#
# - 写しをローカルで編集しない。変更は Makiri 側で行い、固定するコミットを上げる。
# - nupur:check     写しが vendor/nupur.sha256 の内容と一致する（Makiri のチェックアウトは不要）。
# - nupur:upstream  写しが、Makiri のチェックアウトにある固定コミットの内容と一致する。
# - nupur:vendor    固定コミットから写しを作り直す。
# - nupur:lint      Makiri の nupur_lints を拡張に対して実行する。
#
# Makiri のチェックアウトは環境変数 MAKIRI で指定する（なければ ../makiri）。
require "digest"
require "fileutils"
require "open3"
require "shellwords"

NUPUR_REPOSITORY = "https://github.com/takahashim/makiri"
NUPUR_TAG = "v0.17.0.rc3"
NUPUR_COMMIT = "9ec094cf152b1e24cbfb47d604385feb7928c9d6"
NUPUR_UPSTREAM = "ext/makiri/rust/nupur"
# Makiri のライセンス。写しとともに配布する。
NUPUR_LICENSES = %w[LICENSE NOTICE].freeze
NUPUR_DIR = File.join(ROOT, "vendor/nupur")
NUPUR_MANIFEST = File.join(ROOT, "vendor/nupur.sha256")

def makiri_dir
  dir = ENV.fetch("MAKIRI", File.expand_path("../makiri", ROOT))
  abort "nupur: Makiri のチェックアウトがない: #{dir}（環境変数 MAKIRI で指定する）" unless File.directory?(File.join(dir, ".git"))
  dir
end

def makiri_git(*args)
  out, status = Open3.capture2("git", "-C", makiri_dir, *args)
  abort "nupur: git #{args.join(' ')} に失敗した" unless status.success?
  out
end

# 写す対象。[写しの中の相対パス, Makiri の中のパス] の配列。Nupur 自身のテスト用拡張は写さない。
def nupur_upstream_files
  listed = makiri_git("ls-tree", "-r", "--name-only", NUPUR_COMMIT, NUPUR_UPSTREAM).lines.map(&:chomp)
  files = listed.reject { |path| path.start_with?("#{NUPUR_UPSTREAM}/test/") }
                .map { |path| [path.delete_prefix("#{NUPUR_UPSTREAM}/"), path] }
  files + NUPUR_LICENSES.map { |name| [name, name] }
end

def nupur_local_files
  Dir.glob("**/*", File::FNM_DOTMATCH, base: NUPUR_DIR).select { |f| File.file?(File.join(NUPUR_DIR, f)) }.sort
end

def nupur_manifest
  lines = File.readlines(NUPUR_MANIFEST, chomp: true).reject { |l| l.empty? || l.start_with?("#") }
  lines.to_h { |l| l.split("  ", 2).reverse }
end

namespace :nupur do
  desc "Makiri #{NUPUR_TAG} から Nupur の写しを作り直す"
  task :vendor do
    resolved = makiri_git("rev-parse", "#{NUPUR_TAG}^{commit}").strip
    abort "nupur: #{NUPUR_TAG} は #{resolved} を指す。固定したコミットは #{NUPUR_COMMIT}" unless resolved == NUPUR_COMMIT
    FileUtils.rm_rf(NUPUR_DIR)
    entries = nupur_upstream_files.sort.map do |local, upstream|
      content = makiri_git("show", "#{NUPUR_COMMIT}:#{upstream}")
      path = File.join(NUPUR_DIR, local)
      FileUtils.mkdir_p(File.dirname(path))
      File.binwrite(path, content)
      "#{Digest::SHA256.hexdigest(content)}  #{local}"
    end
    header = ["# Nupur の写しの内容。rake nupur:vendor が書く。手で編集しない。",
              "# #{NUPUR_REPOSITORY} #{NUPUR_TAG} #{NUPUR_COMMIT}"]
    File.write(NUPUR_MANIFEST, (header + entries).join("\n") + "\n")
    puts "nupur: #{entries.length} ファイルを #{NUPUR_TAG} から写した"
  end

  desc "Nupur の写しが、記録した内容と一致することを確かめる"
  task :check do
    recorded = File.read(NUPUR_MANIFEST)[/^# #{Regexp.escape(NUPUR_REPOSITORY)} \S+ (\h{40})$/, 1]
    abort "nupur: vendor/nupur.sha256 のコミットは #{recorded.inspect}。固定したコミットは #{NUPUR_COMMIT}" unless recorded == NUPUR_COMMIT
    manifest = nupur_manifest
    local = nupur_local_files
    extra = local - manifest.keys
    missing = manifest.keys - local
    abort "nupur: 写しに余分なファイルがある: #{extra.join(', ')}" unless extra.empty?
    abort "nupur: 写しにファイルが足りない: #{missing.join(', ')}" unless missing.empty?
    changed = local.reject { |f| Digest::SHA256.file(File.join(NUPUR_DIR, f)).hexdigest == manifest[f] }
    abort "nupur: 写しが編集されている: #{changed.join(', ')}。変更は Makiri 側で行い、固定するコミットを上げる" unless changed.empty?
    puts "nupur: 写しの #{local.length} ファイルは、記録した内容（#{NUPUR_TAG}）と一致する"
  end

  desc "Nupur の写しが、Makiri の固定コミットの内容と一致することを確かめる"
  task upstream: :check do
    manifest = nupur_manifest
    upstream = nupur_upstream_files.to_h
    abort "nupur: 写す対象が固定コミットと違う" unless upstream.keys.sort == manifest.keys.sort
    changed = upstream.reject { |local, path| Digest::SHA256.hexdigest(makiri_git("show", "#{NUPUR_COMMIT}:#{path}")) == manifest[local] }
    abort "nupur: 記録した内容が固定コミットと違う: #{changed.keys.join(', ')}" unless changed.empty?
    puts "nupur: 写しは Makiri #{NUPUR_COMMIT[0, 8]} の内容と一致する"
  end
end

# Makiri の固定コミットの lint（ext/makiri/rust/lints）を取り出す場所。
NUPUR_LINTS_DIR = File.join(ROOT, "tmp/makiri-#{NUPUR_COMMIT[0, 12]}")
NUPUR_LINTS = File.join(NUPUR_LINTS_DIR, "ext/makiri/rust/lints")

namespace :nupur do
  # 型で表せない Nupur の規則（GVL を解放した処理が Ruby を実行しない、Ruby の値をヒープに置かない、など）を、
  # Makiri の nupur_lints で検査する（仕様書 §3.2、§14.3）。lint そのものは写さず、Makiri の固定コミットから取り出す。
  # lint は rustc のプラグインなので、cargo-dylint、dylint-link と、lint が固定する nightly が要る。
  desc "Makiri の nupur_lints を拡張に対して実行する"
  task lint: :check do
    unless File.directory?(NUPUR_LINTS)
      FileUtils.mkdir_p(NUPUR_LINTS_DIR)
      sh "git -C #{makiri_dir.shellescape} archive #{NUPUR_COMMIT} ext/makiri/rust/lints | tar -x -C #{NUPUR_LINTS_DIR.shellescape}"
    end
    # cargo は、lint のライブラリだけが変わったときに前回の検査結果を使い回す。毎回検査し直すために触る。
    FileUtils.touch(File.join(ROOT, "ext/fmspec/src/lib.rs"))
    sh({ "RUSTFLAGS" => "-D unfulfilled_lint_expectations" },
       "cargo", "dylint", "--path", NUPUR_LINTS, "--pattern", "nupur_lints", "--no-deps", "--",
       "-p", "fmspec_ext", "--all-features", chdir: ROOT)
    puts "nupur: 拡張は nupur_lints を通った"
  end
end
