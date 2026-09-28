# Copy only completed successful evidence; never run, promote or fabricate a check.
require 'json'
require 'digest'
require 'fileutils'
require 'zlib'
require 'time'
root=File.expand_path('../..',__dir__)
queue=JSON.parse(File.read(ARGV.fetch(0)+'/QUEUE.json'))
dest=__dir__+'/2026-09-29'
FileUtils.mkdir_p(dest)
sha=->(p){Digest::SHA256.file(p).hexdigest}
rows=[]
queue.each do |row|
 name=row.fetch('target'); label=name.split('.').last
 unless row['status']=='passed'
   rows << "| #{label} | Pending | — | — |"
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
 rows << "| [#{label}](2026-09-29/#{label}/RESULT.json) | Passed | #{seconds.to_i} s | #{format('%.2f',r['peak_combined_rss'].to_f/1024**3)} GiB |"
end
summary=<<~MD
# Per-entry Comparator results

These checks concern the [existence contracts](Challenge.lean): a single finite
group witness with the stated order, simplicity and commutativity/noncommutativity.
They do not establish recognition or uniqueness of isomorphism types.
Each passed entry records a real sandboxed Comparator run, statement comparison,
permitted-axiom checking and standard Lean kernel replay. This is not a new Nanoda
run. All runs use the pinned tools in [the reproduction guide](../INDEPENDENT_CHECKERS.md).

Updated #{Time.now.utc.iso8601}. **#{queue.count{|r|r['status']=='passed'}} / #{queue.size} passed.**

| Entry | Result | Elapsed | Peak combined worker RSS |
|---|---|---:|---:|
#{rows.join("\n")}

Passed entries include their actual Challenge and Solution modules, configuration,
unaltered result record, GNU time output and complete compressed Comparator log.
The shared source snapshot covers the release mathematics and pins. Per-run hashes
of runtime Lake setup files are retained in RESULT.json; those machine-local setup
files are recreated by the preparation script and are not bundled. The result
records are execution evidence, not cryptographically signed attestations.

The earlier combined attempt stopped at a memory reserve and is not counted as a
pass. A successful single-target check covers that target and its required proof
dependencies; it does not replace every older structural/catalogue audit target.
MD
File.write(__dir__+'/RESULTS.md',summary)
hashes=Dir.glob(dest+'/**/*').select{|p|File.file?(p)&&File.basename(p)!='SHA256SUMS'}.sort.map{|p|"#{sha.call(p)}  #{p.delete_prefix(dest+'/')}\n"}.join
File.write(dest+'/SHA256SUMS',hashes)
puts "Collected #{queue.count{|r|r['status']=='passed'}} passes"
