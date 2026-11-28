# frozen_string_literal: true

# fmspec の開発タスク。個別のタスクは rakelib/ にある。
#
#   rake            テストと Verus の検証をすべて実行する
#   rake test       Rust のテスト、参照実装のテスト、比較テスト、Ruby のテスト、fmspec-rails のテスト
#   rake verus      中核の証明（変異の検査 verus:mutants は含めない）
#   rake compile    native extension をビルドして lib/fmspec に置く
#   rake nupur:check  Nupur の写しが、固定したコミットの内容と一致することの検査
ROOT = __dir__

# エンジンのcrate。Ruby のヘッダがなくてもビルドできる。
ENGINE_CRATES = %w[fmspec-core fmspec-ir fmspec-search fmspec-api fmspec-cli].freeze
# rustfmt と clippy の対象。Nupur の写し（vendor/nupur）は対象にしない。写しは編集しない。
OWN_CRATES = [*ENGINE_CRATES, "fmspec_ext"].freeze

def cargo(*args)
  sh "cargo", *args, chdir: ROOT
end

def packages(names)
  names.flat_map { |name| ["-p", name] }
end

namespace :test do
  desc "Rust のテスト"
  task :rust do
    cargo "test", *packages(ENGINE_CRATES), "--quiet"
  end

  desc "Ruby のテスト（DSL、IRへの変換、native extension）"
  task ruby: :compile do
    Dir[File.join(ROOT, "test/*_test.rb")].sort.each { |file| ruby file }
  end

  desc "参照実装（Ruby）で仕様書 §17.1.1 の境界ケースを実行する"
  task :reference do
    ruby File.join(ROOT, "reference/test/boundary_test.rb")
  end

  desc "参照実装と fmspec コマンドの結果を突き合わせる"
  task :differential do
    cargo "build", "--quiet"
    ruby File.join(ROOT, "reference/test/differential_test.rb")
  end

  # fmspec-rails は別gemで、依存を fmspec-rails/vendor/bundle に持つ（fmspec-rails で bundle install しておく）。
  desc "fmspec-rails のテスト（Rails アプリケーションでの適合性検査）"
  task rails: :compile do
    dir = File.join(ROOT, "fmspec-rails")
    env = { "BUNDLE_GEMFILE" => File.join(dir, "Gemfile") }
    Dir[File.join(dir, "test/*_test.rb")].sort.each do |file|
      sh env, "bundle", "exec", "ruby", "-Ilib", file, chdir: dir
    end
  end
end

desc "すべてのテスト"
task test: %w[test:rust test:reference test:differential test:ruby test:rails]

desc "clippy と rustfmt"
task :lint do
  cargo "fmt", *packages(OWN_CRATES), "--check"
  cargo "clippy", *packages(OWN_CRATES), "--all-targets", "--all-features", "--quiet", "--", "-D", "warnings"
end

task default: %w[test verus nupur:check]
