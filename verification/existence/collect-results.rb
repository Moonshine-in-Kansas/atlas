# Copy only completed successful evidence; never run, promote or fabricate a check.
require_relative 'contracts'
require 'json'
require 'digest'
require 'fileutils'
require 'zlib'
require 'time'
root=File.expand_path('../..',__dir__)
queue=JSON.parse(File.read(ARGV.fetch(0)+'/QUEUE.json'))
date=ARGV.fetch(1) { Time.now.utc.strftime('%Y-%m-%d') }
raise 'Invalid evidence date' unless date.match?(/\A\d{4}-\d{2}-\d{2}\z/)
dest=__dir__+'/'+date
FileUtils.mkdir_p(dest)
sha=->(p){Digest::SHA256.file(p).hexdigest}
# Use the same display names as the public catalogue; keep evidence paths stable.
catalogue_names=File.read(root+'/CATALOGUE.md').scan(/^\| \[([^\]]+)\]\(#([^)]+)\) \|/).to_h { |display,anchor| [anchor,display] }
family_anchors={'cyclic'=>'cyclic','alternating'=>'alternating','typeA'=>'psl',
  'typeB'=>'b','typeC'=>'c','typeD'=>'d','G2'=>'g2','ReeG2'=>'reeg2'}
registry_path=root+'/verification/existence/registry.json'
registry=JSON.parse(File.read(registry_path))
rows=[]
queue.each do |row|
 name=row.fetch('target'); label=name.split('.').last
 registered=registry.fetch('entries').find{|e|e['declaration']==name}
 raise "Unregistered target: #{name}" unless registered
 anchor=family_anchors.key?(label) ? 'family-'+family_anchors.fetch(label) : 'sporadic-'+label.downcase
 display=catalogue_names.fetch(anchor)
 unless row['status']=='passed'
   rows << "| #{display} | Pending | — | — | [Reference](Challenge.lean) · [Solution](Solution.lean) |"
   next
 end
 src=row.fetch('harness'); r=JSON.parse(File.read(src+'/RESULT.json'))
 AtlasContracts.render(registered).each{|p,bytes|raise "Stale queued contract: #{name}" unless File.binread(src+'/'+p)==bytes.b}
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
 registered['evidence']=target.delete_prefix(root+'/')
 seconds=Time.parse(r['finished_utc'])-Time.parse(r['started_utc'])
 rows << "| [#{display}](#{date}/#{label}/RESULT.json) | Passed | #{seconds.to_i} s | #{format('%.2f',r['peak_combined_rss'].to_f/1024**3)} GiB | [Reference](#{date}/#{label}/Challenge.lean) · [Solution](#{date}/#{label}/Solution.lean) |"
end
summary=<<~MD
# Per-entry Comparator results

These checks concern the [existence contracts](Challenge.lean): a single finite
group witness with the stated order, simplicity and commutativity/noncommutativity.
They do not establish recognition or uniqueness of isomorphism types.

- [Reference statements](Challenge.lean): what must be proved, using only mathlib.
- [Solution file](Solution.lean): the ATLAS imports, chosen groups and existing proofs supplying the witnesses.
- [Strengthened same-order invariants](discriminators/RESULTS.md): involution-class counts for B/C and Sylow-center orders for A₈ and PSL₃(4), attached to the same witnesses.
- [How to reproduce the checks](README.md#running-the-sequential-queue): setup, scripts and sandbox command.

For each passed entry, the last column links its actual individual reference and
solution files. Those solution files use only the imports needed for that entry.
Each passed entry records a real sandboxed Comparator run, statement comparison,
permitted-axiom checking and standard Lean kernel replay. This is not a new Nanoda
run. All runs use the pinned tools in [the reproduction guide](../INDEPENDENT_CHECKERS.md).

Updated #{Time.now.utc.iso8601}. **#{queue.count{|r|r['status']=='passed'}} / #{queue.size} passed.**

| Entry | Result | Elapsed | Peak combined worker RSS | Lean files |
|---|---|---:|---:|---|
#{rows.join("\n")}

Passed entries include their actual Challenge and Solution modules, configuration,
unaltered result record, GNU time output and complete compressed Comparator log.
The shared source snapshot covers the release mathematics and pins. Per-run hashes
of runtime Lake setup files are retained in RESULT.json; those machine-local setup
files are recreated by the preparation script and are not bundled. The result
records are execution evidence, not cryptographically signed attestations.
MD
File.write(__dir__+'/RESULTS.md',summary)
hashes=Dir.glob(dest+'/**/*').select{|p|File.file?(p)&&File.basename(p)!='SHA256SUMS'}.sort.map{|p|"#{sha.call(p)}  #{p.delete_prefix(dest+'/')}\n"}.join
File.write(dest+'/SHA256SUMS',hashes)
puts "Collected #{queue.count{|r|r['status']=='passed'}} passes"

File.write(registry_path,JSON.pretty_generate(registry)+"\n")
puts 'Evidence index updated; run ruby verification/release_metadata.rb refresh after collecting all required scopes.'
