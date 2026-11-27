# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"
require "json_schemer"
require "set"
require_relative "models"
require_relative "../reference/fmspec_reference"
require_relative "../reference/test/model_generator"
require_relative "../reference/test/composite_generator"

# docs/ir.schema.json が、エンジンの受理するIRをすべて受け入れることを確かめる。
# スキーマは構造だけを定めるので、スキーマを満たしてもIR検証で拒否されるIRはある。逆は起きてはならない。
class SchemaTest < Minitest::Test
  SCHEMA = JSONSchemer.schema(Pathname.new(File.join(ROOT, "docs/ir.schema.json")))

  def errors(ir) = SCHEMA.validate(ir).map { |e| e["error"] }

  def assert_schema_valid(ir, label)
    assert_empty errors(ir), "#{label}\n#{JSON.generate(ir)}"
  end

  def loads?(ir) = !Fmspec::Native::Model.load(JSON.generate(ir)).is_a?(String)

  def test_the_schema_is_a_valid_schema
    assert_empty JSONSchemer.validate_schema(JSON.parse(File.read(File.join(ROOT, "docs/ir.schema.json")))).to_a
  end

  def test_examples_follow_the_schema
    Dir[File.join(ROOT, "examples/models/*.json")].each do |path|
      ir = JSON.parse(File.read(path))
      assert loads?(ir), path
      assert_schema_valid(ir, path)
    end
  end

  # DSL の語彙をひととおり使う仕様。
  def everything
    Fmspec.define(:everything) do
      user = enum(:user, :ann, :bob)
      constant :limit, 2
      constant :staff, set_of(user), Set[:ann]
      state :n, int(0..3), initial_in: 0..1
      state :who, option(user), initial: nil
      state :seen, set_of(user), initial_in: [Set[], Set[:bob]]
      state :log, list_of(user, max: 2), initial: []
      state :tally, map_of(user, int(0..2)), initial: {}
      state :pos, record(x: int(0..1), y: int(0..1)), initial: { x: 0, y: 0 }
      ghost :calls, int(0..3), initial: 0
      initially { |s| (s.n < 1) | s.seen.empty?.not_ }

      action :visit, u: user, d: tuple(0..1, bool) do |s, u, d|
        guard (s.n < s.limit) & (s.log.size < 2)
        update n: s.n + d[0], who: some(u), seen: s.seen.add(u), log: s.log.push(u),
               tally: s.tally.put(u, ite(s.tally.key?(u), s.tally[u], 0)), calls: ite(d[1], s.calls, s.calls)
        returns s.n, int(0..3)
        ensures(:grows) { |after, out| after.n >= out }
      end

      action :leave, u: ->(s) { s.seen } do |s, u|
        victim = choose(:victim, s.seen)
        guard s.staff.include?(u).not_ & s.who.some?
        update seen: s.seen.delete(victim), who: nil, log: ite(s.log.empty?, s.log, s.log.shift),
               tally: s.tally.delete(u), pos: { x: s.pos[:y], y: s.pos[:x] }
      end

      invariant(:bounded) { |s| forall(user) { |x| exists(int(0..1)) { |k| let(k + s.n) { |m| m >= 0 } } | x.eq(:ann) } }
      invariant(:arith) { |s| (((s.n / 2) + (s.n % 2)) <= 3) & (s.seen.size <= 2) }
      terminal { |s| s.n.eq(3) }
    end
  end

  def test_dsl_output_follows_the_schema
    assert_schema_valid(everything.to_ir, "everything")
    assert loads?(everything.to_ir)
    TestModels.singleton_methods.each do |name|
      method = TestModels.method(name)
      next unless method.parameters.none? { |kind, _| %i[req block].include?(kind) }

      ir = method.call.to_ir
      assert_schema_valid(ir, name) if loads?(ir)
    end
  end

  def test_generated_models_follow_the_schema
    300.times do |n|
      [ModelGenerator, CompositeGenerator].each do |generator|
        ir = generator.new(7_000_000 + n).model
        assert loads?(ir), "#{generator} #{n}"
        assert_schema_valid(ir, "#{generator} #{n}")
      end
    end
  end

  # 生成したモデルを1か所だけ壊す。エンジンが受理したなら、スキーマも受理しなければならない。
  def test_the_schema_accepts_every_mutant_the_engine_accepts
    rejected_by_schema = 0
    300.times do |n|
      rng = Random.new(8_000_000 + n)
      generator = n.even? ? ModelGenerator : CompositeGenerator
      ir = mutate(generator.new(8_000_000 + n).model, rng)
      if loads?(ir)
        assert_schema_valid(ir, "mutant #{n}")
      elsif !errors(ir).empty?
        rejected_by_schema += 1
      end
    end
    # スキーマが何も拒否しないほど緩い、ということがないようにする。
    assert_operator rejected_by_schema, :>, 100
  end

  def nodes(value, path = [], &block)
    block.call(value, path)
    case value
    when Hash then value.each { |k, v| nodes(v, path + [k], &block) }
    when Array then value.each_with_index { |v, i| nodes(v, path + [i], &block) }
    end
  end

  def mutate(ir, rng)
    ir = JSON.parse(JSON.generate(ir))
    containers = []
    nodes(ir) { |v, path| containers << path if v.is_a?(Hash) || v.is_a?(Array) }
    path = containers[rng.rand(containers.length)]
    node = path.empty? ? ir : ir.dig(*path)
    replacement = ["x", 1.5, nil, [], {}, -1, true, { "int" => 0 }][rng.rand(8)]
    if node.is_a?(Hash)
      key = node.keys.sample(random: rng)
      case rng.rand(3)
      when 0 then node.delete(key)
      when 1 then node["zzz"] = replacement
      else node[key] = replacement if key
      end
    elsif node.empty? || rng.rand < 0.5
      node << replacement
    else
      node.delete_at(rng.rand(node.length))
    end
    ir
  end
end
