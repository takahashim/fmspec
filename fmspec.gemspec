# frozen_string_literal: true

require_relative "lib/fmspec/version"

Gem::Specification.new do |spec|
  spec.name = "fmspec"
  spec.version = Fmspec::VERSION
  spec.authors = ["takahashim"]
  spec.summary = "Executable formal specifications in Ruby, model-checked by a verified Rust engine"
  spec.description = "Write state-transition specifications in a Ruby DSL and check their invariants " \
                     "exhaustively. Verdicts come from an evidence checker verified with Verus."
  spec.required_ruby_version = ">= 3.3"

  # ソースインストールでは、エンジンのcrate、拡張、Nupur の写しをすべて同梱して cargo でビルドする。
  # ネットワークから取るのは crates.io の依存だけで、Makiri のリポジトリは要らない（仕様書 §3.2）。
  spec.files = Dir[
    "lib/**/*.rb",
    "ext/fmspec/{Cargo.toml,extconf.rb}", "ext/fmspec/src/**/*.rs",
    "crates/*/Cargo.toml", "crates/*/src/**/*.rs",
    "vendor/nupur/**/*", "vendor/nupur.sha256",
    "Cargo.toml", "Cargo.lock", "clippy.toml",
    "README.md", "docs/*.md"
  ]
  spec.require_paths = ["lib"]
  spec.extensions = ["ext/fmspec/extconf.rb"]

  # ext/fmspec/extconf.rb が、拡張のビルドに使う。
  spec.add_dependency "rb_sys", "~> 0.9"
end
