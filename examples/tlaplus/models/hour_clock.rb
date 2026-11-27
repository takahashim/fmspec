# frozen_string_literal: true

# vendor/tlaplus-examples/HourClock.tla（Specifying Systems 2章の時計）を DSL で書いたもの。
Fmspec.define(:hour_clock) do
  state :hr, int(1..12), initial_in: 1..12

  action(:tick) { |s| update hr: ite(s.hr.ne(12), s.hr + 1, 1) }
end
