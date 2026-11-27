# frozen_string_literal: true

# 性能測定（仕様書 §13）。bench/models.rb のモデルを fmspec check で検査し、探索と証明書の検査の時間、
# 状態/秒、遷移/秒、ピークRSSを表にする。時間は繰り返しのうち最小のもの。
#
#   cargo build --release
#   ruby -Ilib bench/run.rb [--repeat N] [--fmspec PATH]
require "json"
require "open3"
require "optparse"
require "tmpdir"
require_relative "models"

repeat = 3
fmspec = File.expand_path("../target/release/fmspec", __dir__)
OptionParser.new do |o|
  o.on("--repeat N", Integer) { |n| repeat = n }
  o.on("--fmspec PATH") { |path| fmspec = path }
end.parse!

# fmspec check を実行し、結果のJSONとピークRSS（KB）を返す。
# ピークRSSは、Linux の /proc/PID/status の VmHWM を、終了まで読み続けて得る。ほかの環境では nil。
def run(fmspec, path)
  out = +""
  rss = nil
  status = Open3.popen2(fmspec, "check", path, "--json") do |_in, stdout, wait|
    reader = Thread.new { out << stdout.read }
    proc_status = "/proc/#{wait.pid}/status"
    while wait.alive?
      hwm = begin
        File.read(proc_status)[/^VmHWM:\s+(\d+)/, 1]
      rescue SystemCallError
        nil
      end
      rss = [rss || 0, hwm.to_i].max if hwm
      sleep 0.002
    end
    reader.join
    wait.value
  end
  abort "bench: #{path}: fmspec check が失敗した" unless status.success?
  [JSON.parse(out), rss]
end

rows = Dir.mktmpdir do |dir|
  Bench::MODELS.map do |name, model|
    path = File.join(dir, "#{name}.json")
    File.write(path, model.to_json)
    runs = Array.new(repeat) { run(fmspec, path) }
    best = runs.min_by { |j, _| j["search"]["time_ms"] + j["gate"]["time_ms"] }
    j, rss = best
    search = j["search"]["time_ms"]
    gate = j["gate"]["time_ms"]
    states = j["search"]["visited_states"]
    edges = j["search"]["transitions"]
    {
      model: name, status: j["status"], states: states, transitions: edges,
      search_ms: search.round(1), gate_ms: gate.round(1),
      states_per_s: (states / (search / 1000.0)).round, transitions_per_s: (edges / (search / 1000.0)).round,
      peak_rss_mb: rss && (rss / 1024.0).round(1)
    }
  end
end

keys = rows.first.keys
puts "| #{keys.join(' | ')} |"
puts "|#{keys.map { '---' }.join('|')}|"
rows.each { |r| puts "| #{r.values.join(' | ')} |" }
