# fmspec-rails

[fmspec](../README.md) の仕様を、Railsアプリケーションに結合するためのgem。
DBの変更、Active Jobのキュー、時刻をテストケースの中に閉じ込め、リクエストとジョブの実行を `command` から行えるようにする。

使い方は [docs/rails.md](../docs/rails.md) にある。

```sh
bundle config set --local path vendor/bundle  # 依存を vendor/bundle に入れる（CIと同じ）
bundle install
(cd .. && rake test:rails)
```
