#!/usr/bin/env ruby
# Whole draft library, using the pinned exporter and existing bounded runner.
require_relative '../../verification/existence/chevalley/replay'
require_relative 'monitor'
$stdout.sync = true
ROOT = ChevalleyReplay::ROOT
BASE = File.expand_path(__dir__)
OUT = BASE+'/attempt-'+Time.now.utc.strftime('%Y%m%dT%H%M%S')
FileUtils.mkdir_p(OUT)
def write(name, value) = ChevalleyReplay.write(OUT+'/'+name, value)
def sha(path) = ChevalleyReplay.sha(path)
def source_paths
  (Dir[ROOT+'/Atlas/**/*.lean'] + %w[Atlas.lean lean-toolchain lakefile.toml lake-manifest.json].map { |f| ROOT+'/'+f }).sort
end
state = {status:'preparing', started_utc:Time.now.utc.iso8601,
  scope:'All safe declarations (including private/internal declarations) defined in every current Atlas/**/*.lean module and Atlas.lean, and their complete proof/type dependencies. Unsafe implementation code is inventoried but excluded from mathematical kernel replay.',
  stages:{}, permitted_axioms:ChevalleyContracts::AXIOMS}
write('RESULT.json',state)
leases=[]
begin
  %w[verification/chevalley/.runner.lock verification/existence/.run.lock].each do |p|
    f=File.open(ROOT+'/'+p,File::RDWR)
    raise 'Another verification driver holds the serial lease' unless f.flock(File::LOCK_EX|File::LOCK_NB)
    leases << f
  end
  # Outside the sandbox, /proc covers the host and catches independent drivers.
  active=Dir['/proc/[0-9]*/comm'].filter_map do |p|
    begin
      n=File.read(p).strip
      p if %w[lean lake lean4export nanoda_bin comparator].include?(n)
    rescue Errno::ENOENT,Errno::EACCES
      nil
    end
  end
  raise "Other compute workers active: #{active.join(', ')}" unless active.empty?
  info=ChevalleyReplay.tools
  state[:tools]=info
  state[:source_commit]=ChevalleyReplay.git(ROOT,'rev-parse','HEAD')
  state[:source_remote]=ChevalleyReplay.git(ROOT,'remote','get-url','origin')
  hashes=source_paths.to_h { |p| [p.delete_prefix(ROOT+'/'),sha(p)] }
  write('SOURCE_HASHES.json',hashes)
  FileUtils.cp(BASE+'/ExportAll.lean',OUT+'/ExportAll.lean')
  FileUtils.cp(__FILE__,OUT+'/driver.rb')
  FileUtils.cp(BASE+'/monitor.rb',OUT+'/monitor.rb')
  FileUtils.cp(ROOT+'/verification/existence/chevalley/replay.rb',OUT+'/bounded-runner.rb')
  modules=hashes.keys.grep(/\.lean$/).map { |p| p.delete_suffix('.lean').tr('/','.') }
  if ARGV.first=='--exclude-build-failures'
    previous=File.expand_path(ARGV.fetch(1))
    raise 'Earlier snapshot differs' unless JSON.parse(File.read(previous+'/SOURCE_HASHES.json'))==hashes
    failed=File.read(previous+'/build.log').scan(/^✖.*?Building (Atlas[\w.]*)/).flatten.uniq
    raise 'No explicit failed modules found' if failed.empty?
    missing=modules.reject { |m| File.file?(ROOT+'/.lake/build/lib/lean/'+m.tr('.','/')+'.olean') }
    excluded=(failed+missing).uniq
    loop do
      more=modules.reject { |m| excluded.include?(m) }.select do |m|
        imports=File.read(ROOT+'/'+m.tr('.','/')+'.lean').scan(/^\s*(?:public\s+)?import\s+([^\n]+)/).flatten.flat_map { |s| s.split('--').first.to_s.split }
        (imports & excluded).any?
      end
      break if more.empty?
      excluded.concat(more)
    end
    state[:coverage_gaps]={failed_modules:failed,uncompiled_modules:missing,excluded_modules:excluded.sort,prior_attempt:previous}
    write('COVERAGE_GAPS.json',state[:coverage_gaps])
    modules-=excluded
  end
  File.write(OUT+'/modules.txt',modules.join("\n")+"\n")
  state[:modules]=modules.size
  config=OUT+'/lakefile.toml'
  File.write(config,"weakLeanArgs = [\"-M8704\", \"-j1\"]\n"+File.read(ROOT+'/lakefile.toml'))
  env={'LEAN_NUM_THREADS'=>'2'}
  state[:status]='building'
  write('RESULT.json',state)
  build=DraftMonitor.run(OUT,'build',ROOT,env,
    [ChevalleyReplay::LAKE,'-f',config,'build',*modules.map { |m| '+'+m }])
  state[:stages][:build]=build
  raise 'Library build did not finish successfully; Nanoda not started' unless build[:status]=='process-passed'
  path,st=Open3.capture2(ChevalleyReplay::LAKE,'env','printenv','LEAN_PATH',chdir:ROOT)
  raise 'Unable to obtain Lean search path' unless st.success?
  exporter_lib=File.dirname(File.dirname(info.fetch('lean4export').fetch(:binary)))+'/lib/lean'
  env['LEAN_PATH']=exporter_lib+':'+path.strip
  lean=Open3.capture2(ChevalleyReplay::LAKE,'env','which','lean',chdir:ROOT).first.strip
  proof=OUT+'/proofs.ndjson'
  state[:status]='exporting'
  write('RESULT.json',state)
  export=DraftMonitor.run(OUT,'export',ROOT,env,
    [lean,'-j1','-M8704','--run',OUT+'/ExportAll.lean',OUT+'/modules.txt',OUT+'/inventory.jsonl'],stdout:proof)
  state[:stages][:export]=export
  raise 'Export did not complete; Nanoda not started' unless export[:status]=='process-passed' && File.size?(proof)
  export[:sha256]=sha(proof)
  export[:bytes]=File.size(proof)
  cfg={export_file_path:proof,permitted_axioms:ChevalleyContracts::AXIOMS,
    unpermitted_axiom_hard_error:true,num_threads:1,nat_extension:true,string_extension:true,
    print_success_message:true,print_axioms:true,unsafe_permit_all_axioms:false}
  write('nanoda-config.json',cfg)
  state[:status]='checking'
  write('RESULT.json',state)
  check=DraftMonitor.run(OUT,'nanoda',ROOT,env,[info.fetch('nanoda').fetch(:binary),OUT+'/nanoda-config.json'])
  state[:stages][:nanoda]=check
  count=File.read(OUT+'/nanoda.log')[/Checked (\d+) declarations with no errors/,1]
  raise 'Nanoda did not finish with its success marker' unless check[:status]=='process-passed' && count
  raise 'Proof export changed' unless sha(proof)==export[:sha256]
  state[:checked_declarations]=count.to_i
  raise 'Checker binary changed' unless info.all? { |_,v| sha(v.fetch(:binary))==v.fetch(:sha256) }
  state[:status]=state[:coverage_gaps] ? 'partial-pass' : 'passed'
rescue StandardError => e
  state[:status]='incomplete'
  state[:reason]=e.message
ensure
  if defined?(hashes) && hashes
    current=source_paths.to_h { |p| [p.delete_prefix(ROOT+'/'),sha(p)] }
    state[:sources_unchanged]=current==hashes
    unless state[:sources_unchanged]
      state[:status]='invalidated-source-change'
    end
  end
  state[:finished_utc]=Time.now.utc.iso8601
  write('RESULT.json',state)
  leases.each(&:close)
  puts JSON.pretty_generate(state.reject { |k,_| k==:stages || k==:tools }.merge(evidence:OUT+'/RESULT.json'))
end
exit(state[:status]=='passed' ? 0 : 1)
