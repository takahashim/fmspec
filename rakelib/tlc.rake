# frozen_string_literal: true

require "digest"
require "fileutils"

# TLC との比較テスト（reference/test/tlc_test.rb）。
#
# - tlc:fetch  固定したリリースの tla2tools.jar を取得し、SHA-256 を確かめる。
# - test:tlc   fmspec の結果を、TLA+ に変換したモデルを TLC で検査した結果と突き合わせる。
#
# tla2tools.jar は環境変数 TLA2TOOLS で指定できる。指定がなければ tmp/tlc に取得したものを使う。
# 実行には Java 11 以上が要る。
#
# v1.8.0 は master から作り直され続けるビルドで、中身が固定されない。安定版のリリースに固定する。
TLA2TOOLS_VERSION = "v1.7.4"
TLA2TOOLS_SHA256 = "936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"
TLA2TOOLS_URL = "https://github.com/tlaplus/tlaplus/releases/download/#{TLA2TOOLS_VERSION}/tla2tools.jar"
TLA2TOOLS_JAR = File.join(ROOT, "tmp/tlc/#{TLA2TOOLS_VERSION}/tla2tools.jar")

def tla2tools_jar
  ENV.fetch("TLA2TOOLS", TLA2TOOLS_JAR)
end

namespace :tlc do
  desc "固定したリリースの tla2tools.jar を tmp/tlc に取得する"
  task :fetch do
    next if File.file?(TLA2TOOLS_JAR) && Digest::SHA256.file(TLA2TOOLS_JAR).hexdigest == TLA2TOOLS_SHA256

    FileUtils.mkdir_p(File.dirname(TLA2TOOLS_JAR))
    part = "#{TLA2TOOLS_JAR}.part"
    sh "curl", "--fail", "--silent", "--show-error", "--location", "--output", part, TLA2TOOLS_URL
    actual = Digest::SHA256.file(part).hexdigest
    unless actual == TLA2TOOLS_SHA256
      FileUtils.rm_f(part)
      abort "tlc: tla2tools.jar の SHA-256 が #{actual}。固定した値は #{TLA2TOOLS_SHA256}"
    end
    File.rename(part, TLA2TOOLS_JAR)
  end
end

namespace :test do
  desc "fmspec と TLC の結果を突き合わせる（Java が要る）"
  task :tlc do
    Rake::Task["tlc:fetch"].invoke unless ENV["TLA2TOOLS"]
    cargo "build", "--quiet", "-p", "fmspec-cli"
    sh({ "TLA2TOOLS" => tla2tools_jar }, "ruby", File.join(ROOT, "reference/test/tlc_test.rb"))
  end
end
