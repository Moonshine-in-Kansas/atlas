require 'json'
require 'digest'
require 'open3'
require 'fileutils'
require 'time'
require 'zlib'
require 'set'
ROOT='/home/gerald/atlas'
TASK=File.expand_path('..',__dir__)
CANDIDATE=TASK+'/candidate'
CACHE=ROOT+'/.publication-tools/twisted-e6-foundations-20261019/export'
LEAN='/home/gerald/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean'
OUT=__dir__+'/cache-audit-'+Time.now.utc.strftime('%Y%m%dT%H%M%SZ')
raise 'Existing audit output' if File.exist?(OUT)
FileUtils.mkdir_p(OUT)
$stdout.sync=true
module ChevalleyReplay
  def self.memory
    s=File.read('/proc/meminfo')
    %w[MemTotal MemAvailable SwapFree].to_h { |k|[k,s[/^#{k}:\s+(\d+)/,1].to_i*1024] }
  end
  def self.sha(p)=Digest::SHA256.file(p).hexdigest
  def self.write(p,x)=File.write(p,JSON.pretty_generate(x)+"\n")
  def self.stop(pid)
    Process.kill('TERM',-pid) rescue nil
    sleep 2
    Process.kill('KILL',-pid) rescue nil
  end
end
require ROOT+'/claude/comparator-draft-20261025/run-20261025T000133/monitor'
require CANDIDATE+'/verification/policy'
def capture(*cmd)
  out,err,status=Open3.capture3({'GIT_OPTIONAL_LOCKS'=>'0'},*cmd)
  raise err unless status.success?
  out
end
def sha(p)=Digest::SHA256.file(p).hexdigest
source_hashes=JSON.parse(File.read(CANDIDATE+'/verification/release-candidate/SOURCE_HASHES.json'))
original=JSON.parse(File.read(TASK+'/EXPORT_PROVENANCE.json')).fetch('source_hashes')
roots=JSON.parse(File.read(CANDIDATE+'/verification/roots.json'))
record={status:'preparing',started_utc:Time.now.utc.iso8601,scope:'Fresh root elaboration and complete compiled type/proof dependency inspection using a read-only source-bound cache; not a fresh project rebuild or independent kernel replay',
  roots:roots.size,cache_source:CACHE,allowed_axioms:AtlasVerification::AXIOMS,steps:[]}
save=-> {File.write(OUT+'/RESULT.json',JSON.pretty_generate(record)+"\n")}
save.call
begin
  # Reuse the established serial lease, without creating anything outside claude/.
  lock=File.open(ROOT+'/verification/chevalley/.runner.lock',File::RDWR)
  raise 'Another build/audit holds the serial lease' unless lock.flock(File::LOCK_EX|File::LOCK_NB)
  free=capture('df','-Pk',OUT).lines.last.split[3].to_i*1024
  raise 'Insufficient disk reserve for bounded audit' if free<1024**3
  record[:disk_available_before]=free
  original.each { |p,h|raise "Cache source changed: #{p}" unless sha(CACHE+'/'+p)==h }
  source_hashes.each { |p,h|raise "Candidate changed: #{p}" unless sha(CANDIDATE+'/'+p)==h }
  packages=JSON.parse(File.read(CANDIDATE+'/lake-manifest.json')).fetch('packages')
  pins=packages.to_h do |p|
    dir=ROOT+'/.lake/packages/'+p.fetch('name')
    rev=capture('git','-C',dir,'rev-parse','HEAD').strip
    raise "Changed dependency #{p['name']}" unless rev==p.fetch('rev')
    raise "Dirty dependency #{p['name']}" unless capture('git','-C',dir,'status','--porcelain','--untracked-files=no').empty?
    [p['name'],rev]
  end
  record[:dependency_revisions]=pins
  inventory=[];artifacts={}
  original.keys.grep(/\.lean\z/).each do |p|
    base=CACHE+'/.lake/build/lib/lean/'+p.delete_suffix('.lean')
    trace=JSON.parse(File.read(base+'.trace'))
    raise "Synthetic build trace #{p}" if trace['synthetic']
    input=trace.fetch('inputs').find { |x|x.is_a?(Array) && x[0].is_a?(String) && x[0].end_with?('/'+p) }
    raise "Missing source trace #{p}" unless input && input[1].match?(/\A[0-9a-f]{16}\z/)
    inventory<<['text',CACHE+'/'+p,input[1]]
    outputs=trace.fetch('outputs').fetch('o')
    raise "Unexpected compiled artifact shape #{p}" unless outputs.size==1 && outputs.first.end_with?('.olean')
    expected=outputs.first.delete_suffix('.olean')
    inventory<<['binary',base+'.olean',expected]
    artifacts[base+'.olean']=sha(base+'.olean')
  end
  File.write(OUT+'/CACHE_HASHES.tsv',inventory.map { |r|r.join("\t")+"\n" }.join)
  File.write(OUT+'/SOURCE_HASHES.json',JSON.pretty_generate(source_hashes)+"\n")
  File.write(OUT+'/CACHE_ARTIFACTS.json',JSON.pretty_generate(artifacts)+"\n")
  File.write(OUT+'/roots.json',JSON.pretty_generate(roots)+"\n")
  path=(packages.reverse.map { |p|ROOT+'/.lake/packages/'+p['name']+'/.lake/build/lib/lean' }+[CACHE+'/.lake/build/lib/lean']).join(':')
  env={'LEAN_NUM_THREADS'=>'2','LEAN_PATH'=>path}
  opts=['-j1','-M8192','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-Dweak.linter.mathlibStandardSet=true','-DmaxSynthPendingDepth=3']
  run=->(name,cwd,cmd) do
    r=DraftMonitor.run(OUT,name,cwd,env,cmd)
    record[:steps]<<{name:name,record:name+'.json',status:r[:status]};save.call
    raise "#{name}: #{r[:status]} #{r[:guard_stop]}" unless r[:status]=='process-passed'
  end
  run.call('cache-hashes',ROOT,[LEAN,'-j1','-M1024','--run',__dir__+'/CacheHashes.lean',OUT+'/CACHE_HASHES.tsv'])
  run.call('root-elaboration',CANDIDATE,[LEAN,*opts,'--root='+CANDIDATE,CANDIDATE+'/Atlas.lean'])
  run.call('audit-root-elaboration',CANDIDATE,[LEAN,*opts,'--root='+CANDIDATE,CANDIDATE+'/Atlas/Audit.lean'])
  text=File.read(CANDIDATE+'/verification/Extract.lean.in')
  replacements={'@@IMPORTS@@'=>'import Atlas','@@TARGETS@@'=>'#['+roots.map { |r|'('+[r['declaration'],r['module'],r['kind']].map { |s|JSON.generate(s) }.join(', ')+')' }.join(', ')+']',
    '@@OUTPUT@@'=>JSON.generate(OUT),'@@FULL@@'=>'true','@@DEFINITIONS@@'=>'false'}
  replacements.each { |a,b|text=text.gsub(a) { b } }
  File.write(OUT+'/Extract.lean',text)
  run.call('full-dependency-extraction',CANDIDATE,[LEAN,*opts,OUT+'/Extract.lean'])
  raise 'Incomplete extraction' unless File.read(OUT+'/full-dependency-extraction.log').include?("SHARED EXTRACTION COMPLETE: #{roots.size} targets")
  records=File.readlines(OUT+'/declarations.jsonl').map { |s|JSON.parse(s) }
  raise 'Root mismatch' unless records.map { |r|r['declaration'] }.sort==roots.map { |r|r['declaration'] }.sort
  nodes={}
  File.foreach(OUT+'/dependencies.jsonl') do |s|
    n=JSON.parse(s);raise 'Duplicate dependency' if nodes.key?(n['name']);nodes[n['name']]=n
  end
  AtlasVerification.check_policy({'allowed_axioms'=>AtlasVerification::AXIOMS},records,nodes)
  source_hashes.each { |p,h|raise "Candidate source changed during audit #{p}" unless sha(CANDIDATE+'/'+p)==h }
  original.each { |p,h|raise "Cache source changed during audit #{p}" unless sha(CACHE+'/'+p)==h }
  artifacts.each { |p,h|raise "Read-only artifact changed #{p}" unless sha(p)==h }
  record.merge!(status:'passed-source-bound-cache-audit',dependency_nodes:nodes.size,
    axioms:records.flat_map { |r|r['axioms'] }.uniq.sort,cache_artifacts_unchanged:true,
    sources_unchanged:true,fresh_project_rebuild:false,independent_replay:false)
rescue=>e
  record.merge!(status:'incomplete',error:e.message)
ensure
  record[:finished_utc]=Time.now.utc.iso8601
  %w[root-elaboration.log audit-root-elaboration.log full-dependency-extraction.log dependencies.jsonl].each do |p|
    next unless File.file?(OUT+'/'+p)
    Zlib::GzipWriter.open(OUT+'/'+p+'.gz') { |g|g.mtime=0;File.open(OUT+'/'+p,'rb') { |f|IO.copy_stream(f,g) } }
  end
  save.call
  File.write(__dir__+'/LATEST_CACHE_AUDIT.txt',OUT+"\n")
  puts JSON.pretty_generate(record)
  lock&.flock(File::LOCK_UN)
  lock&.close
end
exit(record[:status]=='passed-source-bound-cache-audit' ? 0 : 1)
