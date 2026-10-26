#!/usr/bin/env ruby
# Serial replay of all existing, reviewed Comparator contracts. No new specifications.
require_relative '../../verification/existence/chevalley/replay'
require_relative '../../verification/existence/contracts'
require_relative '../nanoda-draft-20261024/monitor'
$stdout.sync=true
ROOT=ChevalleyReplay::ROOT
BASE=File.expand_path(__dir__)
OUT=BASE+'/run-'+Time.now.utc.strftime('%Y%m%dT%H%M%S')
FileUtils.mkdir_p(OUT)
def sha(p) = ChevalleyReplay.sha(p)
def write(p,r) = ChevalleyReplay.write(p,r)
def current_sources
  (Dir[ROOT+'/Atlas/**/*.lean']+%w[Atlas.lean lean-toolchain lakefile.toml lake-manifest.json].map { |p| ROOT+'/'+p }).sort.to_h { |p| [p.delete_prefix(ROOT+'/'),sha(p)] }
end
state={status:'preparing',started_utc:Time.now.utc.iso8601,scope:'All 45 existing Comparator targets: 34 existence/discriminator statements, 9 Chevalley model contracts, and 2 concrete-model catalogue isomorphism statements. This is reference-statement comparison and Lean default-kernel replay, not another Nanoda replay or new recognition result.',checks:[]}
save=-> { write(OUT+'/RESULT.json',state) }
save.call
leases=[]
begin
  %w[verification/chevalley/.runner.lock verification/existence/.run.lock].each do |p|
    f=File.open(ROOT+'/'+p,File::RDWR)
    raise 'Another verification driver holds the serial lease' unless f.flock(File::LOCK_EX|File::LOCK_NB)
    leases<<f
  end
  active=Dir['/proc/[0-9]*/comm'].filter_map do |p|
    begin
      p if %w[lean lake lean4export nanoda_bin comparator].include?(File.read(p).strip)
    rescue Errno::ENOENT,Errno::EACCES
      nil
    end
  end
  raise "Other compute workers active: #{active.join(', ')}" unless active.empty?
  info=ChevalleyReplay.tools
  state[:tools]=info
  state[:source_commit]=ChevalleyReplay.git(ROOT,'rev-parse','HEAD')
  state[:source_remote]=ChevalleyReplay.git(ROOT,'remote','get-url','origin')
  sources=current_sources
  write(OUT+'/SOURCE_HASHES.json',sources)
  refs=%w[verification/existence/Challenge.lean verification/existence/Solution.lean verification/existence/discriminators/Challenge.lean verification/existence/discriminators/Solution.lean verification/existence/registry.json verification/existence/contracts.rb verification/existence/check.rb verification/existence/chevalley/registry.json verification/existence/chevalley/check.rb verification/comparisons/Reference.lean verification/comparisons/Solution.lean verification/comparisons/comparator.json]
  refs+=Dir[ROOT+'/verification/existence/chevalley/{A,B,C,D,E6,E7,E8,F4,G2}/*'].select { |p| File.file?(p) }.map { |p| p.delete_prefix(ROOT+'/') }
  references=refs.sort.to_h { |p| [p,sha(ROOT+'/'+p)] }
  write(OUT+'/REFERENCE_SOURCE_HASHES.json',references)
  FileUtils.cp(__FILE__,OUT+'/driver.rb')
  FileUtils.cp(BASE+'/../nanoda-draft-20261024/monitor.rb',OUT+'/monitor.rb')
  validations={}
  [%w[ruby verification/existence/check.rb],%w[ruby verification/existence/chevalley/check.rb],%w[ruby verification/comparisons/prepare.rb --check]].each do |cmd|
    output,status=Open3.capture2e(*cmd,chdir:ROOT)
    validations[cmd.join(' ')]=output
    raise "Contract validation failed: #{output}" unless status.success?
  end
  write(OUT+'/CONTRACT_VALIDATION.json',validations)
  specs=%w[E6 E7 E8 A B C D F4 G2].map do |key|
    path=ROOT+'/verification/existence/chevalley/'+key
    files=%w[Challenge.lean Solution.lean comparator.json].to_h { |p| [p,File.read(path+'/'+p)] }
    {id:'Chevalley-'+key,files:files,reference_boundary:'Mathlib-only imports; explicit Chevalley-model witness in solution'}
  end
  specs+=AtlasContracts.entries.map do |r|
    {id:r.fetch('declaration').tr('.','-'),files:AtlasContracts.render(r),reference_boundary:'Mathlib-only imports; reviewed existence/discriminator contract'}
  end
  specs<<{id:'Catalogue-isomorphism',files:%w[Reference.lean Solution.lean comparator.json].to_h { |p| [p,File.read(ROOT+'/verification/comparisons/'+p)] },reference_boundary:'Shared concrete model registry and normalization definitions; two isomorphism/nonisomorphism reference statements'}
  specs.each do |spec|
    dir=OUT+'/'+spec[:id]
    FileUtils.mkdir_p(dir)
    spec[:files].each { |p,b| File.write(dir+'/'+p,b) }
    FileUtils.cp(ROOT+'/lean-toolchain',dir+'/lean-toolchain')
    config=JSON.parse(spec[:files].fetch('comparator.json'))
    raise 'Unexpected contract options' unless config['definition_names']==[] && config['permitted_axioms'].sort==AtlasContracts::AXIOMS.sort && !config['enable_nanoda'] && !config['external_kernels']
    libs=[config.fetch('challenge_module'),config.fetch('solution_module')]
    lakefile="name = \"AtlasComparatorContract\"\nversion = \"0.1.0\"\npackagesDir = #{JSON.generate(ROOT+'/.lake/packages')}\n[leanOptions]\nmaxRecDepth = 10000\n[[require]]\nname = \"Atlas\"\npath = #{JSON.generate(ROOT)}\n"
    libs.each { |name| lakefile+="[[lean_lib]]\nname = #{JSON.generate(name)}\nmoreLeanArgs = [\"-j1\", \"-M8704\"]\n" }
    File.write(dir+'/lakefile.toml',lakefile)
    manifest=JSON.parse(File.read(ROOT+'/lake-manifest.json'))
    manifest['packagesDir']=ROOT+'/.lake/packages'
    manifest['name']='AtlasComparatorContract'
    manifest['packages'].each { |p| p['inherited']=true }
    manifest['packages'].unshift({'type'=>'path','scope'=>'','name'=>'Atlas','manifestFile'=>'lake-manifest.json','inherited'=>false,'dir'=>ROOT,'configFile'=>'lakefile.toml'})
    write(dir+'/lake-manifest.json',manifest)
    paths=spec[:files].keys+%w[lean-toolchain lakefile.toml lake-manifest.json]
    inputs=paths.to_h { |p| [p,sha(dir+'/'+p)] }
    state[:checks]<<{id:spec[:id],directory:dir,targets:config.fetch('theorem_names'),reference_boundary:spec[:reference_boundary],status:'pending',input_hashes:inputs}
  end
  raise 'Unexpected target count' unless state[:checks].sum { |c| c[:targets].size }==45
  state[:target_count]=45
  state[:status]='running'
  save.call
  bins=info.transform_values { |v| v.fetch(:binary) }
  env={'LEAN_NUM_THREADS'=>'2','COMPARATOR_LANDRUN'=>bins['landrun'],'COMPARATOR_LEAN4EXPORT'=>bins['lean4export'],
    'PATH'=>[File.dirname(bins['landrun']),File.dirname(bins['lean4export']),File.dirname(ChevalleyReplay::LAKE),ENV.fetch('PATH')].join(':')}
  state[:checks].each_with_index do |check,index|
    raise 'Sources changed before next check' unless current_sources==sources && references.all? { |p,h| sha(ROOT+'/'+p)==h }
    dir=check[:directory]
    check[:status]='running'
    check[:started_utc]=Time.now.utc.iso8601
    save.call
    puts "[#{index+1}/#{state[:checks].size}] #{check[:id]}"
    stage=DraftMonitor.run(dir,'comparator-check',dir,env,[ChevalleyReplay::LAKE,'env',bins['comparator'],'comparator.json'])
    check[:stage]=stage
    log=File.file?(dir+'/comparator-check.log') ? File.read(dir+'/comparator-check.log') : ''
    unchanged=check[:input_hashes].all? { |p,h| sha(dir+'/'+p)==h } && current_sources==sources && references.all? { |p,h| sha(ROOT+'/'+p)==h }
    passed=stage[:status]=='process-passed' && log.include?('Your solution is okay!') && log.include?('Lean default kernel accepts the solution') && unchanged
    check.merge!(status:passed ? 'passed' : 'incomplete',inputs_unchanged:unchanged,finished_utc:Time.now.utc.iso8601)
    write(dir+'/RESULT.json',check)
    save.call
    puts "#{check[:id]}: #{check[:status]}"
    raise 'Inputs changed during check' unless unchanged
    # Independent contracts can still pass after a contract-specific failure.
    # Stop only for machine-wide pressure or unavailable starting headroom.
    break if stage[:status]=='blocked-memory' || stage[:guard_stop].to_s.match?(/pressure|reserve|four compute/)
  end
  state[:sources_unchanged]=current_sources==sources && references.all? { |p,h| sha(ROOT+'/'+p)==h }
  state[:binaries_unchanged]=info.all? { |_,v| sha(v.fetch(:binary))==v.fetch(:sha256) }
  state[:passed_targets]=state[:checks].select { |c| c[:status]=='passed' }.sum { |c| c[:targets].size }
  state[:status]=state[:passed_targets]==45 && state[:sources_unchanged] && state[:binaries_unchanged] ? 'passed' : 'incomplete'
rescue StandardError=>e
  state[:status]='incomplete'
  state[:reason]=e.message
ensure
  state[:finished_utc]=Time.now.utc.iso8601
  save.call
  leases.each(&:close)
  puts JSON.pretty_generate(state.reject { |k,_| [:checks,:tools].include?(k) }.merge(evidence:OUT+'/RESULT.json'))
end
exit(state[:status]=='passed' ? 0 : 1)
