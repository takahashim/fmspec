# frozen_string_literal: true

# vendor/tlaplus-examples/SlidingPuzzles.tla（Klotski、箱入り娘の一種）を DSL で書いたもの。盤面は 4 x 5 である。
# TLA+ の board は駒（マスの集合）の集合で、同じ形の駒は区別しない。DSL の集合の要素に集合は使えないので、
# 駒の形ごとに、駒の基準のマス（左上）の集合で表す。形が同じ駒は区別しないので、この対応は一対一である。
#
#   縦長（1 x 2）の駒が4つ、正方形（2 x 2）が1つ、横長（2 x 1）が1つ、1マスの駒が4つ
#
# TLA+ の Next は、空いたマスを1つ選び、その隣の駒を空いたマスの方向へ1マス動かす。
# これは、どれかの駒を、行き先のマスがすべて盤面の中で、ほかの駒と重ならないときに1マス動かすことと同じである。
# 不変条件 klotski_goal（正方形が下の中央にない）が破れることが、パズルの解にあたる。
Fmspec.define(:sliding_puzzles) do
  w = 4
  h = 5
  pos = tuple(int(0..(w - 1)), int(0..(h - 1)))
  # 形ごとの、基準のマスから見た駒のマスの位置。
  shapes = { tall: [[0, 0], [0, 1]], square: [[0, 0], [1, 0], [0, 1], [1, 1]], wide: [[0, 0], [1, 0]], unit: [[0, 0]] }
  state :tall, set_of(pos), initial: Set[[0, 0], [3, 0], [0, 2], [3, 2]]
  state :square, pos, initial: [1, 0]
  state :wide, pos, initial: [1, 2]
  state :unit, set_of(pos), initial: Set[[1, 3], [2, 3], [0, 4], [3, 4]]

  # 基準のマスが anchor の、形 shape の駒が、マス (x, y) を覆う。
  covers = lambda do |shape, anchor, x, y|
    any(*shapes.fetch(shape).map { |dx, dy| (anchor[0] + dx).eq(x) & (anchor[1] + dy).eq(y) })
  end
  # マス (x, y) を、動かす駒（形 shape の基準のマス anchor）以外の駒が覆う。
  # 形の選び分けは Ruby の側で行う。記号式の左に Ruby の true を置くと、TrueClass#& が呼ばれて式が消える。
  taken = lambda do |s, shape, anchor, x, y|
    terms = { tall: s.tall, unit: s.unit }.map do |kind, anchors|
      anchors.any? { |b| kind == shape ? b.ne(anchor) & covers.(kind, b, x, y) : covers.(kind, b, x, y) }
    end
    terms << covers.(:square, s.square, x, y) unless shape == :square
    terms << covers.(:wide, s.wide, x, y) unless shape == :wide
    any(*terms)
  end
  # 駒を (dx, dy) だけ動かした先のマスが、すべて盤面の中で、ほかの駒と重ならない。
  free = lambda do |s, shape, anchor, dx, dy|
    all(*shapes.fetch(shape).map do |ox, oy|
      x = anchor[0] + ox + dx
      y = anchor[1] + oy + dy
      (x >= 0) & (x < w) & (y >= 0) & (y < h) & taken.(s, shape, anchor, x, y).not_
    end)
  end
  directions = [[1, 0], [0, 1], [-1, 0], [0, -1]]
  step = ->(anchor, dx, dy) { [anchor[0] + dx, anchor[1] + dy] }

  directions.each do |dx, dy|
    tag = { [1, 0] => :right, [0, 1] => :down, [-1, 0] => :left, [0, -1] => :up }.fetch([dx, dy])

    action :"move_tall_#{tag}", a: ->(s) { s.tall } do |s, a|
      guard free.(s, :tall, a, dx, dy)
      update tall: s.tall.delete(a).add(step.(a, dx, dy))
    end

    action :"move_unit_#{tag}", a: ->(s) { s.unit } do |s, a|
      guard free.(s, :unit, a, dx, dy)
      update unit: s.unit.delete(a).add(step.(a, dx, dy))
    end

    action :"move_square_#{tag}" do |s|
      guard free.(s, :square, s.square, dx, dy)
      update square: step.(s.square, dx, dy)
    end

    action :"move_wide_#{tag}" do |s|
      guard free.(s, :wide, s.wide, dx, dy)
      update wide: step.(s.wide, dx, dy)
    end
  end

  invariant(:klotski_goal) { |s| s.square.ne([1, 3]) }
end
