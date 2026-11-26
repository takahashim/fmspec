# frozen_string_literal: true

# fmspec の開発タスク。個別のタスクは rakelib/ にある。
#
#   rake            テストと Verus の検証をすべて実行する
#   rake test       Rust のテスト、参照実装のテスト、比較テスト
#   rake verus      中核の証明と、証明が空虚でないことの検査
ROOT = __dir__

def cargo(*args)
  sh "cargo", *args, chdir: ROOT
end

namespace :test do
  desc "Rust のテスト"
  task :rust do
    cargo "test", "--workspace", "--quiet"
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
end

desc "すべてのテスト"
task test: %w[test:rust test:reference test:differential]

desc "clippy と rustfmt"
task :lint do
  cargo "fmt", "--all", "--check"
  cargo "clippy", "--workspace", "--all-targets", "--quiet", "--", "-D", "warnings"
end

task default: %w[test verus]
