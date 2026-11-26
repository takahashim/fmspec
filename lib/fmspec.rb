# frozen_string_literal: true

require_relative "fmspec/version"
# native extension。Fmspec::Native と Fmspec::InternalError を定義する。
require_relative "fmspec/fmspec"

unless Fmspec::Native.version == Fmspec::VERSION
  raise LoadError, "fmspec: native extension のバージョン（#{Fmspec::Native.version}）が gem（#{Fmspec::VERSION}）と一致しません。" \
                   "ビルドし直してください"
end

require_relative "fmspec/dsl"
