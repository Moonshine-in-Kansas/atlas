require_relative '../../verification/existence/chevalley/replay'
require_relative 'monitor'
$stdout.sync=true
root=ChevalleyReplay::ROOT
base=File.expand_path(__dir__)
source=File.expand_path(ARGV.fetch(0))
out=base+'/filtered-'+Time.now.utc.strftime('%Y%m%dT%H%M%S')
FileUtils.mkdir_p(out)
state={status:'preparing',started_utc:Time.now.utc.iso8601,source_attempt:source,
  scope:'All 59500 ATLAS theorems and all other kernel-safe declarations in the built 4957-module library, with full proof/type dependencies. Exactly 45 compiler-generated partial _unsafe_rec implementations are excluded; no theorem or mathematical definition is replaced or weakened.',stages:{}}
save=-> { ChevalleyReplay.write(out+'/RESULT.json',state) }
save.call
leases=[]
begin
  %w[verification/chevalley/.runner.lock verification/existence/.run.lock].each do |p|
    f=File.open(root+'/'+p,File::RDWR)
    raise 'Another checker holds the serial lease' unless f.flock(File::LOCK_EX|File::LOCK_NB)
    leases<<f
  end
  hashes=JSON.parse(File.read(source+'/SOURCE_HASHES.json'))
  unchanged=-> { hashes.all? { |p,h| File.file?(root+'/'+p) && ChevalleyReplay.sha(root+'/'+p)==h } && (Dir[root+'/Atlas/**/*.lean'].map { |p| p.delete_prefix(root+'/') }+['Atlas.lean']).sort==hashes.keys.grep(/\.lean$/).sort }
  raise 'Source snapshot changed' unless unchanged.call
  prior=JSON.parse(File.read(source+'/RESULT.json'))
  raise 'No successful original export' unless prior.dig('stages','export','status')=='process-passed'
  expected=prior.fetch('stages').fetch('export').fetch('sha256')
  raise 'Original export changed' unless ChevalleyReplay.sha(source+'/proofs.ndjson')==expected
  info=ChevalleyReplay.tools
  state[:tools]=info
  state[:original_export_sha256]=expected
  state[:source_commit]=prior['source_commit']
  %w[SOURCE_HASHES.json COVERAGE_GAPS.json modules.txt].each { |f| FileUtils.cp(source+'/'+f,out+'/'+f) }
  %w[replay-filtered.rb filter-partial.rb monitor.rb].each { |f| FileUtils.cp(base+'/'+f,out+'/'+f) }
  proof=out+'/proofs.ndjson'
  env={'LEAN_NUM_THREADS'=>'2'}
  state[:status]='filtering-compiler-implementations'
  save.call
  r=DraftMonitor.run(out,'filter',root,env,['ruby',base+'/filter-partial.rb',source,out],stdout:proof)
  state[:stages][:filter]=r
  raise 'Filtering failed' unless r[:status]=='process-passed'
  state[:export_bytes]=File.size(proof)
  state[:export_sha256]=ChevalleyReplay.sha(proof)
  state[:roots]=File.foreach(out+'/inventory.jsonl').count
  cfg={export_file_path:proof,permitted_axioms:ChevalleyContracts::AXIOMS,
    unpermitted_axiom_hard_error:true,num_threads:1,nat_extension:true,string_extension:true,
    print_success_message:true,print_axioms:true,unsafe_permit_all_axioms:false}
  ChevalleyReplay.write(out+'/nanoda-config.json',cfg)
  state[:status]='checking'
  save.call
  r=DraftMonitor.run(out,'nanoda',root,env,[info.fetch('nanoda').fetch(:binary),out+'/nanoda-config.json'])
  state[:stages][:nanoda]=r
  count=File.read(out+'/nanoda.log')[/Checked (\d+) declarations with no errors/,1]
  raise 'Nanoda did not finish with a success marker' unless r[:status]=='process-passed' && count
  raise 'Filtered export changed' unless ChevalleyReplay.sha(proof)==state[:export_sha256]
  raise 'Original export changed' unless ChevalleyReplay.sha(source+'/proofs.ndjson')==expected
  raise 'Checker changed' unless info.all? { |_,v| ChevalleyReplay.sha(v.fetch(:binary))==v.fetch(:sha256) }
  state[:checked_declarations]=count.to_i
  state[:status]='passed-for-built-library'
rescue StandardError=>e
  state[:status]='incomplete'
  state[:reason]=e.message
ensure
  state[:sources_unchanged]=unchanged.call if defined?(unchanged) && unchanged
  state[:status]='invalidated-source-change' if state[:sources_unchanged]==false
  state[:finished_utc]=Time.now.utc.iso8601
  save.call
  leases.each(&:close)
  puts JSON.pretty_generate(state.reject { |k,_| [:stages,:tools].include?(k) }.merge(evidence:out+'/RESULT.json'))
end
exit(state[:status]=='passed-for-built-library' ? 0 : 1)
