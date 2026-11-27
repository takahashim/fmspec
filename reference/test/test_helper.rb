# frozen_string_literal: true

require "minitest/autorun"
require "json"
require_relative "../fmspec_reference"

ROOT = File.expand_path("../..", __dir__)
I64_MAX = 2**63 - 1

# テスト用のモデル。Rust 側のテスト（crates/fmspec-cli/tests/common）と同じものを、独立に書いてある。
module Models
  module_function

  def tickets
    JSON.parse(File.read(File.join(ROOT, "examples/models/tickets.json")))
  end

  def tickets_without_guard
    tickets.tap { |ir| ir["actions"][0].delete("guard") }
  end

  def counter(max, actions)
    { "ir_version" => 1, "name" => "counter",
      "states" => [{ "name" => "x", "type" => { "int" => { "min" => 0, "max" => max } }, "initial" => { "int" => 0 } }],
      "actions" => actions }
  end

  def stay
    { "name" => "stay", "updates" => [{ "target" => 0, "expr" => { "var" => 0 } }] }
  end

  def go(name, from, to)
    { "name" => name, "guard" => { "eq" => [{ "var" => 0 }, { "int" => from }] },
      "updates" => [{ "target" => 0, "expr" => { "int" => to } }] }
  end

  def big(invariant)
    { "ir_version" => 1, "name" => "big",
      "states" => [{ "name" => "big", "type" => { "int" => { "min" => 0, "max" => I64_MAX } },
                     "initial" => { "int" => I64_MAX } }],
      "invariants" => [{ "name" => "p", "expr" => invariant }] }
  end

  def overflowing
    { "gt" => [{ "add" => [{ "var" => 0 }, { "int" => 1 }] }, { "int" => 0 }] }
  end

  def responder
    label = ->(v) { { "enum" => { "type" => "result", "variant" => v } } }
    { "ir_version" => 1, "name" => "responder",
      "enums" => [{ "name" => "result", "variants" => %w[success forbidden] }],
      "states" => [{ "name" => "x", "type" => { "int" => { "min" => 0, "max" => 0 } }, "initial" => { "int" => 0 } }],
      "actions" => [{
        "name" => "request",
        "params" => [{ "name" => "id", "type" => { "int" => { "min" => 7, "max" => 7 } } }],
        "choices" => [{ "name" => "allowed", "type" => { "bool" => {} } }],
        "updates" => [],
        "output" => { "type" => { "enum" => "result" },
                      "expr" => { "ite" => [{ "choice" => 0 }, label.("success"), label.("forbidden")] } }
      }],
      "contracts" => [{ "name" => "succeeds", "action" => "request",
                        "expr" => { "eq" => [{ "output" => {} }, label.("success")] } }] }
  end
end

def reference(ir)
  FmspecReference::Model.new(ir)
end
