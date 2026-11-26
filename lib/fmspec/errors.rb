# frozen_string_literal: true

module Fmspec
  # fmspec が利用者に報告するエラーの親。
  class Error < StandardError; end

  # 仕様の記述の誤り。型の合わない式、未定義の名前、記号ブロックで使えない構文など。
  class BuildError < Error; end

  # エンジンのIR検証がモデルを拒否した。DSL が先に検出できなかった誤りである。
  class InvalidModelError < Error; end
end
