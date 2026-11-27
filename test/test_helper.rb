# frozen_string_literal: true

$LOAD_PATH.unshift(File.expand_path("../lib", __dir__))
require "minitest/autorun"
require_relative "models"

ROOT = File.expand_path("..", __dir__)

# IRからソース位置を除く。期待するIRと比べるときに使う。
def without_sources(value)
  case value
  when Hash then value.reject { |k, _| k == "source" }.transform_values { |v| without_sources(v) }
  when Array then value.map { |v| without_sources(v) }
  else value
  end
end
