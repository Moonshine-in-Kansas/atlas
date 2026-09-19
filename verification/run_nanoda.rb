# Reproduce Nanoda replay; build first. Tool paths supplied by the caller.
require 'json'
require 'digest'
require 'fileutils'
require 'open3'
require 'time'
root=File.expand_path('..',__dir__)
release=root
stamp=Time.now.utc.strftime('%Y%m%dT%H%M%SZ')
out=root+'/verification/results/nanoda-'+stamp
FileUtils.mkdir_p(out)
refs=JSON.parse(File.read(release+'/verification/roots.json'))
names=refs.map{|r|r.fetch('declaration')}.uniq
raise 'Empty selection' if names.empty?
files=(Dir.glob(release+'/Atlas/**/*.lean')+[release+'/Atlas.lean',release+'/lean-toolchain',release+'/lakefile.toml',release+'/lake-manifest.json',release+'/verification/roots.json']).sort
hashes=files.to_h{|p|[p.delete_prefix(release+'/'),Digest::SHA256.file(p).hexdigest]}
File.write(out+'/SOURCE_HASHES.json',JSON.pretty_generate(hashes)+"\n")
FileUtils.cp(release+'/verification/roots.json',out+'/roots.json')
exporter=File.expand_path(ENV.fetch('LEAN4EXPORT'))
nanoda=File.expand_path(ENV.fetch('NANODA'))
commit,st=Open3.capture2('git','-C',release,'rev-parse','HEAD');raise 'Cannot read commit' unless st.success?
r={status:'exporting',started_utc:Time.now.utc.iso8601,source_commit:commit.strip,roots:names.size,scope:'All selected release catalogue/comparison roots and their complete exported dependencies; direct Nanoda replay, not Comparator challenge comparison and not every unrelated imported declaration',expected_nanoda_commit:'4c544ed4099c8227f07d5de77ad1e69fb0740a27',nanoda_sha256:Digest::SHA256.file(nanoda).hexdigest,exporter_sha256:Digest::SHA256.file(exporter).hexdigest,lean:'4.34.0-rc2',threads:1,allowed_axioms:%w[propext Classical.choice Quot.sound]}
save=-> {File.write(out+'/RESULT.json',JSON.pretty_generate(r)+"\n")};save.call
begin
 Dir.chdir(release) do
  File.open(out+'/proofs.ndjson','w') do |f|
   File.open(out+'/export.log','w') do |e|
    ok=system({'LEAN_NUM_THREADS'=>'2'},'/usr/bin/time','-v','-o',out+'/export.time',ENV.fetch('LAKE','lake'),'env',exporter,'Atlas','--',*names,out:f,err:e)
    raise 'Export failed; see export.log/export.time' unless ok
   end
  end
 end
 r[:export_finished_utc]=Time.now.utc.iso8601
 r[:export_bytes]=File.size(out+'/proofs.ndjson')
 r[:export_sha256]=Digest::SHA256.file(out+'/proofs.ndjson').hexdigest
 config={export_file_path:out+'/proofs.ndjson',permitted_axioms:r[:allowed_axioms],unpermitted_axiom_hard_error:true,num_threads:1,nat_extension:true,string_extension:true,print_success_message:true,print_axioms:true,pp_declars:names,pp_to_stdout:true,unknown_pp_declar_hard_error:true,unsafe_permit_all_axioms:false}
 File.write(out+'/config.json',JSON.pretty_generate(config)+"\n")
 r[:status]='checking';save.call
 File.open(out+'/check.log','w') do |f|
  raise 'Nanoda rejected or failed; see check.log/check.time' unless system('/usr/bin/time','-v','-o',out+'/check.time',nanoda,out+'/config.json',out:f,err:[:child,:out])
 end
 log=File.read(out+'/check.log')
 count=log[/Checked (\d+) declarations with no errors/,1]
 raise 'Missing success marker' unless count
 hashes.each{|p,h|raise "Source changed during run: #{p}" unless Digest::SHA256.file(release+'/'+p).hexdigest==h}
 r[:checked_declarations]=count.to_i
 r[:status]='passed'
rescue StandardError=>e
 r[:status]='failed';r[:error]=e.message
ensure
 r[:finished_utc]=Time.now.utc.iso8601;save.call
 puts JSON.pretty_generate(r)
end
exit(r[:status]=='passed' ? 0 : 1)
