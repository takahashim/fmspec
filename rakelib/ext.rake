# frozen_string_literal: true

# native extension のビルド（開発用）。
#
# cargo で cdylib を作り、lib/fmspec/fmspec.<DLEXT> に置く。gem のインストールでは
# ext/fmspec/extconf.rb（rb_sys）が同じcrateをビルドする。
#
#   FMSPEC_PROFILE     dev（既定）または release
#   FMSPEC_TEST_HOOKS  0 にすると、テスト用のメソッドを入れない
require "rbconfig"
require "fileutils"

EXT_PROFILE = ENV.fetch("FMSPEC_PROFILE", "dev")
EXT_PATH = File.join(ROOT, "lib/fmspec/fmspec.#{RbConfig::CONFIG['DLEXT']}")

desc "native extension をビルドして lib/fmspec に置く"
task :compile do
  args = ["rustc", "-p", "fmspec_ext", "--profile", EXT_PROFILE]
  args += ["--features", "test-hooks"] unless ENV["FMSPEC_TEST_HOOKS"] == "0"
  args << "--"
  # 拡張は、rb_* のシンボルを持つ Ruby のプロセスに読み込まれる。macOS では、未定義のシンボルを
  # 読み込み時に解決するようリンカに伝える（gem のインストールでは rb_sys が同じ指定をする）。
  args += ["-C", "link-arg=-Wl,-undefined,dynamic_lookup"] if RbConfig::CONFIG["target_os"].include?("darwin")
  cargo(*args)
  target = ENV.fetch("CARGO_TARGET_DIR", File.join(ROOT, "target"))
  dir = File.join(target, EXT_PROFILE == "dev" ? "debug" : EXT_PROFILE)
  built = Dir[File.join(dir, "libfmspec.{dylib,so}"), File.join(dir, "fmspec.dll")].first
  abort "compile: ビルドした拡張が #{dir} に見つからない" unless built
  FileUtils.cp(built, EXT_PATH)
  puts "compile: #{EXT_PATH}"
end
