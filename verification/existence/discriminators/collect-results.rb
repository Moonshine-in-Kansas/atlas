# Copy only completed successful evidence; never run, promote or fabricate a check.
require 'json'
require 'digest'
require 'fileutils'
require 'zlib'
require 'time'
root=File.expand_path('../../..',__dir__)
queue=JSON.parse(File.read(ARGV.fetch(0)+'/QUEUE.json'))
dest=__dir__+'/2026-09-29'
FileUtils.mkdir_p(dest)
sha=->(p){Digest::SHA256.file(p).hexdigest}
displays={'typeB'=>'Bₙ(q)','typeC'=>'Cₙ(q)','alternating8'=>'A₈ ≅ A₃(2)','psl3Four'=>'A₂(4) = PSL₃(4)'}
rows=[]
queue.each do |row|
 name=row.fetch('target'); label=name.split('.').last
 display=displays.fetch(label)
 unless row['status']=='passed'
   rows << "| #{display} | Pending | — | — | [Reference](Challenge.lean) · [Solution](Solution.lean) |"
   next
 end
 src=row.fetch('harness'); r=JSON.parse(File.read(src+'/RESULT.json'))
 raise 'Not a successful check' unless r['status']=='passed' && r['exit_code']==0 && r['inputs_unchanged'] && !r['memory_guard_stop']
 raise 'Log hash mismatch' unless sha.call(src+'/comparator.log')==r['log_sha256']
 %w[Challenge.lean Solution.lean comparator.json].each{|p|raise 'Changed input' unless sha.call(src+'/'+p)==r.fetch('files').fetch(p)}
 sources=JSON.parse(File.read(src+'/SOURCE_HASHES.json'))
 raise 'Changed release sources' unless sources.all?{|p,h|sha.call(root+'/'+p)==h}
 target=dest+'/'+label; FileUtils.mkdir_p(target)
 %w[Challenge.lean Solution.lean comparator.json RESULT.json time.txt].each do |p|
  dst=target+'/'+p
  raise "Changed retained evidence #{dst}" if File.exist?(dst) && sha.call(dst)!=sha.call(src+'/'+p)
  FileUtils.cp(src+'/'+p,dst) unless File.exist?(dst)
 end
 unless File.exist?(target+'/comparator.log.gz')
  Zlib::GzipWriter.open(target+'/comparator.log.gz'){|z|z.mtime=0;File.open(src+'/comparator.log','rb'){|f|IO.copy_stream(f,z)}}
 end
 FileUtils.cp(src+'/SOURCE_HASHES.json',dest+'/SOURCE_HASHES.json') unless File.exist?(dest+'/SOURCE_HASHES.json')
 raise 'Inconsistent source snapshots' unless sha.call(src+'/SOURCE_HASHES.json')==sha.call(dest+'/SOURCE_HASHES.json')
 seconds=Time.parse(r['finished_utc'])-Time.parse(r['started_utc'])
 rows << "| [#{display}](2026-09-29/#{label}/RESULT.json) | Passed | #{seconds.to_i} s | #{format('%.2f',r['peak_combined_rss'].to_f/1024**3)} GiB | [Reference](2026-09-29/#{label}/Challenge.lean) · [Solution](2026-09-29/#{label}/Solution.lean) |"
end
summary=<<~MD
# Same-order groups: strengthened existence checks

[Reference statements](Challenge.lean) · [Solution proofs and imports](Solution.lean) · [Reproduction instructions](README.md)

Each statement asserts finiteness, exact order, simplicity, noncommutativity and
the displayed invariant **for the same existentially quantified group**.
The reference depends only on mathlib and explicitly defines the conjugacy-class
count; it does not import ATLAS or prescribe a group construction.

| Contract | Additional invariant |
|---|---|
| Bₙ(q) | For odd q, k₂(G) = n |
| Cₙ(q) | For odd q, k₂(G) = floor(n/2) + 1 |
| A₈ ≅ A₃(2), order 20,160 | Every Sylow-2 subgroup has center of order 2 |
| A₂(4) = PSL₃(4), order 20,160 | Every Sylow-2 subgroup has center of order 4 |

Here k₂ counts conjugacy classes of elements of order exactly two, excluding the
identity. For odd q and n≥3, the B/C counts differ. For the order-20,160 pair,
Sylow conjugacy and invariance of center order under isomorphism distinguish the
two witnesses. These checks distinguish these same-order pairs; they do not
claim a general recognition or uniqueness theorem for every group of that order.
The B/C contracts retain their original all-characteristic admissible ranges,
with the additional class-count clause conditional on odd characteristic.

Updated #{Time.now.utc.iso8601}. **#{queue.count{|r|r['status']=='passed'}} / #{queue.size} passed.**

| Entry | Result | Elapsed | Peak combined worker RSS | Lean files |
|---|---|---:|---:|---|
#{rows.join("\n")}

Each passed record includes statement comparison, allowed-axiom checking and
standard Lean kernel replay by the real sandboxed Comparator. This is not a
Nanoda run. The source snapshot, tool revisions, input hashes, complete compressed
log and time report accompany the result. Runtime Lake setup files are recreated
by the preparation script; their original hashes remain in RESULT.json.

The [original 23 existence checks](../RESULTS.md) are preserved separately and
are not retrospectively relabeled as having checked these stronger statements.
MD
File.write(__dir__+'/RESULTS.md',summary)
hashes=Dir.glob(dest+'/**/*').select{|p|File.file?(p)&&File.basename(p)!='SHA256SUMS'}.sort.map{|p|"#{sha.call(p)}  #{p.delete_prefix(dest+'/')}\n"}.join
File.write(dest+'/SHA256SUMS',hashes)
puts "Collected #{queue.count{|r|r['status']=='passed'}} passes"
