require_relative '../../verification/existence/chevalley/replay'
require 'open3'
base=File.expand_path(__dir__)
out=base+'/filtered-20261024T144223'
root=ChevalleyReplay::ROOT
result=JSON.parse(File.read(out+'/RESULT.json'))
process=JSON.parse(File.read(out+'/nanoda.json'))
config=JSON.parse(File.read(out+'/nanoda-config.json'))
coverage=JSON.parse(File.read(out+'/EXPORT_COVERAGE.json'))
log=File.read(out+'/nanoda.log')
raise 'Checker process did not pass' unless process['exit_code']==0 && process['status']=='process-passed' && process['guard_stop'].nil?
expected="Checked 139617 declarations with no typechecker errors, 1 pretty printer errors: [\n    \"Unable to print axioms\",\n]\n"
raise 'Unexpected checker output' unless log==expected
raise 'Unexpected checker configuration' unless config['unpermitted_axiom_hard_error']==true && config['unsafe_permit_all_axioms']==false && config['permitted_axioms'].sort==ChevalleyContracts::AXIOMS.sort
raise 'Unexpected pretty-printer configuration' unless config['print_axioms']==true && !config['pp_to_stdout'] && !config['pp_output_path']
raise 'Incomplete export coverage' unless coverage['inventoried_roots']==69383 && coverage['exported_roots_seen']==69383 && coverage['remaining_roots']==0 && coverage['exported_declarations_including_dependencies']==139617
hashes=JSON.parse(File.read(out+'/SOURCE_HASHES.json'))
paths=(Dir[root+'/Atlas/**/*.lean'].map { |p| p.delete_prefix(root+'/') }+%w[Atlas.lean lean-toolchain lakefile.toml lake-manifest.json]).sort
raise 'Changed source inventory' unless paths==hashes.keys.sort
raise 'Changed sources' unless hashes.all? { |p,h| ChevalleyReplay.sha(root+'/'+p)==h }
raise 'Changed filtered export' unless ChevalleyReplay.sha(out+'/proofs.ndjson')==result['export_sha256']
raise 'Changed original export' unless ChevalleyReplay.sha(result['source_attempt']+'/proofs.ndjson')==result['original_export_sha256']
info=ChevalleyReplay.tools
raise 'Changed checker tools' unless info.all? { |k,v| result['tools'][k]['sha256']==v[:sha256] }
raise 'Changed checker log' unless ChevalleyReplay.sha(out+'/nanoda.log')==process['log_sha256']
names=['']
axioms=[]
Open3.popen2('rg','-e','"in":','-e','^\{"axiom":',out+'/proofs.ndjson') do |input,output,thread|
  input.close
  output.each_line do |line|
    r=JSON.parse(line)
    if r.key?('in')
      c=r['str'] || r.fetch('num')
      prefix=names.fetch(c.fetch('pre'))
      segment=c['str'] || c.fetch('i').to_s
      names[r['in']]=prefix.empty? ? segment : prefix+'.'+segment
    else
      a=r.fetch('axiom')
      raise 'Unsafe axiom' if a['isUnsafe']
      axioms << names.fetch(a.fetch('name'))
    end
  end
  raise 'Axiom extraction failed' unless thread.value.success?
end
raise 'Unexpected exported axioms' unless axioms.sort==ChevalleyContracts::AXIOMS.sort
record={status:'passed-kernel-check-with-pretty-printer-warning',recorded_utc:Time.now.utc.iso8601,
  scope_file:'SCOPE.json',checked_declarations:139617,atlas_roots:69383,atlas_theorems:59500,
  axioms:axioms.sort,checker_exit_code:0,typechecker_errors:0,
  checker_started_utc:process['started_utc'],checker_finished_utc:process['finished_utc'],
  peak_owned_rss_and_swap:process['peak_owned_rss_and_swap'],
  reporting_warning:'print_axioms was enabled without a pretty-printer destination. The pinned Nanoda main checks all declarations before pretty-printing; its explicit no-typechecker-errors message and exit 0 certify the kernel replay. The wrapper expected the no-errors message and therefore recorded incomplete. That original receipt is preserved.',
  original_wrapper_receipt:'RESULT.json',checker_receipt:'nanoda.json',checker_log:'nanoda.log',
  sources_unchanged:true,proof_exports_unchanged:true,checker_binaries_unchanged:true,
  filtered_export_sha256:result['export_sha256'],original_export_sha256:result['original_export_sha256'],
  validator_sha256:ChevalleyReplay.sha(__FILE__),nanoda_revision:info['nanoda'][:revision],
  reporting_source_hashes:%w[src/main.rs src/pretty_printer.rs src/util.rs].to_h { |p| [p,ChevalleyReplay.sha(ChevalleyReplay::TOOLS+'/nanoda/'+p)] }}
ChevalleyReplay.write(out+'/KERNEL_RESULT.json',record)
FileUtils.cp(__FILE__,out+'/record-kernel-result.rb')
puts JSON.pretty_generate(record)
