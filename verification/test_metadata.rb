# Lightweight corruption/regression checks. No Lean, network, or evidence writes.
require_relative 'release_metadata'
require 'fileutils'
require 'open3'
require 'time'
out=ARGV.fetch(0) { abort 'Usage: ruby verification/test_metadata.rb NEW_EXTERNAL_OUTPUT_DIRECTORY' }
out=File.expand_path(out)
root=AtlasReleaseMetadata::ROOT
abort 'Keep test outputs outside the candidate' if out==root || out.start_with?(root+'/')
abort 'Refusing to overwrite test outputs' if File.exist?(out)
FileUtils.mkdir_p(out)
class TestInputs < AtlasContracts::Index
  def initialize(root,overrides={})
    @overrides=overrides
    super(root)
  end
  def read(p)=@overrides.key?(p) ? @overrides.fetch(p) : super
end
base=AtlasContracts::Index.new(root)
results=[]
reject=lambda do |label,pattern,&body|
  begin
    body.call
  rescue StandardError=>e
    raise "#{label}: wrong rejection: #{e.message}" unless e.message.match?(pattern)
    results<<{test:label,result:'passed',rejection:e.message}
  else
    raise "#{label}: unsafe input was accepted"
  end
end
change=lambda do |p,&f|
  j=base.json(p);f.call(j);{p=>JSON.pretty_generate(j)+"\n"}
end
gate=lambda { |overrides={}|AtlasReleaseMetadata::Gate.new(root,reader:TestInputs.new(root,overrides)) }
g=gate.call;g.validate_sources!;g.validate_measurement!;g.validate_cache!;g.validate_history!;g.validate_acceptance!
raise 'Current pending requirements disappeared' unless g.blockers.size==6 && g.contracts[:open]==AtlasContracts::DEFERRED
results<<{test:'Unchanged candidate validates and retains six explicit acceptance requirements',result:'passed'}
source='Atlas/Families/Cyclic/Basic.lean'
reject.call('Changed proof source',/Sources or dependency pins changed/) { gate.call(source=>base.read(source)+"\n").validate_sources! }
reject.call('Changed toolchain pin',/Sources or dependency pins changed/) { gate.call('lean-toolchain'=>"leanprover/lean4:v0.0.0\n").validate_sources! }
o=change.call('verification/roots.json') { |j|j.pop }
reject.call('Omitted audit root',/audit roots differ/) { gate.call(o).validate_sources! }
%w[family.E6 exceptional.Tits].each do |id|
  o=change.call('catalogue/catalogue.json') { |j|j['entries'].reject! { |e|e['id']==id } }
  reject.call("Omitted catalogue model #{id}",/primary model coverage/) { TestInputs.new(root,o).validate! }
end
o=change.call('verification/existence/registry.json') do |j|
  j['entries'].each do |r|
    r['primary_catalogue_contract']=!r['primary_catalogue_contract'] if %w[AtlasExistence.F4 AtlasExistenceChevalley.F4].include?(r['declaration'])
  end
end
reject.call('Chevalley F4 substituted for Albert default',/Wrong concrete model binding/) { TestInputs.new(root,o).validate! }
o=change.call('verification/existence/registry.json') { |j|j['entries'].pop }
reject.call('Omitted reviewed contract',/target selection changed/) { TestInputs.new(root,o).validate! }
first=base.entries.find { |r|r['declaration']=='AtlasExistence.cyclic' }
%w[reference_file configuration].each do |kind|
  p=first.fetch('evidence')+'/'+first.fetch(kind)
  reject.call("Changed reviewed #{kind}",/Changed original artifact/) { TestInputs.new(root,p=>base.read(p)+"\n").validate! }
end
p=first.fetch('evidence')+'/comparator-check.log.gz'
reject.call('Corrupted Comparator log',/Changed original artifact/) { TestInputs.new(root,p=>base.read(p)+"x").validate! }
stopped={'status'=>'process-passed','exit_code'=>0,'signal'=>nil,'guard_stop'=>'owned memory cap'}
reject.call('Memory-stopped process falsely marked passed',/memory-stopped process/) { gate.call.process!(stopped) }
dir=base.json('verification/current.json').dig('supplemental_cache_audit','directory')
%w[fresh_project_rebuild independent_replay].each do |flag|
  r=base.json(dir+'/RESULT.json');r[flag]=true
  bytes=JSON.pretty_generate(r)+"\n"
  bundle=base.json(dir+'/BUNDLE.json');bundle['files']['RESULT.json']=Digest::SHA256.hexdigest(bytes)
  bbytes=JSON.pretty_generate(bundle)+"\n"
  index=base.json('verification/current.json');index['supplemental_cache_audit']['bundle_sha256']=Digest::SHA256.hexdigest(bbytes)
  over={dir+'/RESULT.json'=>bytes,dir+'/BUNDLE.json'=>bbytes,'verification/current.json'=>JSON.pretty_generate(index)+"\n"}
  reject.call("Cache audit falsely promoted: #{flag}",/Cache audit cannot be promoted/) { x=gate.call(over);x.validate_sources!;x.validate_cache! }
end
o=change.call('verification/current.json') { |j|j['deferred_contracts']=[] }
reject.call('Silently removed pending targets',/Deferred targets must remain explicitly open/) { gate.call(o).validate_history! }
%w[../README.md /etc/passwd verification/../README.md].each do |p|
  reject.call("Unsafe path #{p}",/Unsafe evidence path/) { base.path(p) }
end
newout=out+'/cyclic-harness'
stdout,stderr,status=Open3.capture3('ruby',root+'/verification/existence/prepare-queue.rb',newout,'AtlasExistence.cyclic')
raise "Portable preparer failed: #{stderr}" unless status.success?
base.render(first).each do |p,s|
  raise "Prepared contract changed: #{p}" unless File.binread(newout+'/AtlasExistence.cyclic/'+p)==s
end
raise 'Harness unexpectedly built' if Dir.exist?(newout+'/AtlasExistence.cyclic/.lake')
results<<{test:'Portable harness preserves exact reviewed inputs; no build',result:'passed'}
AtlasContracts::DEFERRED.each do |target|
  dir=out+'/refused-'+target
  _,err,st=Open3.capture3('ruby',root+'/verification/existence/prepare-queue.rb',dir,target)
  raise 'Deferred target prepared' if st.success? || File.exist?(dir) || !err.include?('deferred targets remain open')
  results<<{test:"Deferred harness refused: #{target}",result:'passed'}
end
_,err,st=Open3.capture3('ruby',root+'/verification/existence/prepare-queue.rb',newout,'AtlasExistence.cyclic')
raise 'Existing harness overwritten' if st.success? || !err.include?('overwrite')
results<<{test:'Existing harness cannot be overwritten',result:'passed'}
report={status:'passed-tooling-regressions',utc:Time.now.utc.iso8601,tests:results,
  scope:'Metadata safeguards only; no proof replay or new mathematical evidence'}
File.write(out+'/RESULT.json',JSON.pretty_generate(report)+"\n")
puts "PASS: #{results.size} metadata safeguards and portable harness checks. No Lean or independent checker ran."
