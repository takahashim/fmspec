# frozen_string_literal: true

# fmspec の native extension のビルド。隣のcrate（fmspec_ext）を cargo に渡す。
# エンジンのcrate（crates/）とバインディング層（vendor/nupur）は、同じワークスペースから一緒にビルドされる。
require "mkmf"
require "rb_sys/mkmf"

create_rust_makefile("fmspec/fmspec") do |r|
  # 拡張だけを cdylib としてビルドする。
  r.extra_cargo_args = ["--crate-type", "cdylib"]
  r.profile = ENV.fetch("FMSPEC_CARGO_PROFILE", "release").to_sym
end
