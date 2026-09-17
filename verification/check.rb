require 'json';require 'digest';require 'fileutils';require 'zlib';require 'time';require 'open3'
require_relative 'policy'
Dir.chdir(File.expand_path('..',__dir__))
ENV['LEAN_NUM_THREADS']='2'
lake=ENV.fetch('LAKE','lake');out='verification/results'
FileUtils.mkdir_p(out)
refs=JSON.parse(File.read('verification/roots.json'))
sources=(Dir.glob('Atlas/**/*.lean')+%w[Atlas.lean lean-toolchain lakefile.toml lake-manifest.json]).sort.to_h{|p|[p,Digest::SHA256.file(p).hexdigest]}
result={started_utc:Time.now.utc.iso8601,status:'started',roots:refs.size,scope:'All catalogue roles, properties, auxiliary order references and comparison interfaces; transitive type and proof dependencies',checking:'Project-source build with pinned public dependency cache, followed by compiled-declaration audit; not an independent comparator or fresh mathlib source rebuild'}
begin
 File.open(out+'/build.log','w'){|f|raise 'Build failed' unless system(lake,'build',out:f,err:[:child,:out])}
version,version_status=Open3.capture2(lake,'env','lean','--version')
raise 'Lean version query failed' unless version_status.success?
expected=File.read('lean-toolchain').strip.split(':').last.delete_prefix('v')
raise 'Wrong Lean toolchain' unless version.include?(expected)
result[:lean_version]=version.strip
package_pins=JSON.parse(File.read('lake-manifest.json')).fetch('packages')
verify_packages=lambda do
  package_pins.to_h do |pkg|
    raise 'Non-Git dependency needs review' unless pkg['type']=='git'
    path='.lake/packages/'+pkg.fetch('name')
    rev,status=Open3.capture2('git','-C',path,'rev-parse','HEAD')
    raise "Wrong dependency revision #{pkg['name']}" unless status.success?&&rev.strip==pkg.fetch('rev')
    dirty,status=Open3.capture2('git','-C',path,'status','--porcelain=v1','--untracked-files=no')
    raise "Dirty dependency #{pkg['name']}" unless status.success?&&dirty.empty?
    [pkg['name'],rev.strip]
  end
end
result[:dependency_revisions]=verify_packages.call
 template=File.read('verification/Extract.lean.in')
 replacements={'@@IMPORTS@@'=>'import Atlas', '@@TARGETS@@'=>'#['+refs.map{|r|'('+[r['declaration'],r['module'],r['kind']].map{|s|JSON.generate(s)}.join(', ')+')'}.join(', ')+']','@@OUTPUT@@'=>JSON.generate(out),'@@FULL@@'=>'true','@@DEFINITIONS@@'=>'false'}
 replacements.each{|k,v|template=template.gsub(k){v}}
 File.write(out+'/Extract.lean',template)
 File.open(out+'/statements.log','w'){|f|raise 'Extraction failed' unless system(lake,'env','lean',out+'/Extract.lean',out:f,err:[:child,:out])}
 raise 'Incomplete extraction' unless File.read(out+'/statements.log').include?("SHARED EXTRACTION COMPLETE: #{refs.size} targets")
 records=File.readlines(out+'/declarations.jsonl').map{|l|JSON.parse(l)}
 raise 'Root mismatch' unless records.map{|r|r['declaration']}.sort==refs.map{|r|r['declaration']}.sort
 nodes={};File.foreach(out+'/dependencies.jsonl'){|l|j=JSON.parse(l);raise 'Duplicate dependency' if nodes.key?(j['name']);nodes[j['name']]=j}
 AtlasVerification.check_policy({'allowed_axioms'=>%w[propext Classical.choice Quot.sound]},records,nodes)
 sources.each{|p,h|raise "Changed source #{p}" unless Digest::SHA256.file(p).hexdigest==h}
 raise 'Dependency changed during audit' unless verify_packages.call==result[:dependency_revisions]
 result[:status]='passed';result[:axioms]=records.flat_map{|r|r['axioms']}.uniq.sort;result[:dependency_nodes]=nodes.size
rescue StandardError=>e
 result[:status]='failed';result[:error]=e.message
ensure
 result[:finished_utc]=Time.now.utc.iso8601
 File.write(out+'/RESULT.json',JSON.pretty_generate(result)+"\n")
 File.write(out+'/SOURCE_HASHES.json',JSON.pretty_generate(sources)+"\n")
 %w[statements.log dependencies.jsonl build.log].each do |n|
  next unless File.file?(out+'/'+n)
  Zlib::GzipWriter.open(out+'/'+n+'.gz'){|g|g.mtime=0;File.open(out+'/'+n,'rb'){|f|IO.copy_stream(f,g)}}
 end
 puts JSON.pretty_generate(result)
end
exit(result[:status]=='passed' ? 0 : 1)
