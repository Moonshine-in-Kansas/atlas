require_relative '../prepare-queue'
if ARGV==['--check']
  rows=AtlasContracts.entries.select{|r|r['scope']=='discriminators'}
  rows.each{|r|AtlasContracts.render(r)}
  puts "PASS: #{rows.size} reviewed same-witness contracts; mathlib-only reference; no solution placeholders."
else
  prepare_atlas_queue('discriminators',ARGV.fetch(0))
end
