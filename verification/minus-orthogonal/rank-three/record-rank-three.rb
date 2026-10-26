#!/usr/bin/env ruby
# Add a rank-three supplement without changing the immutable stable proof bundle.
require 'json'
require 'digest'
require 'zlib'
require 'fileutils'
require_relative '../../docs/catalogue/manage'
abort 'Usage: record-rank-three.rb RUN_PATHS.json PRINCIPAL_RUN' unless ARGV.size==2
paths=JSON.parse(File.read(ARGV[0]));principal=ARGV[1]
abort 'Wrong scope set' unless paths.keys.sort==%w[all-ranks-order all-ranks-simplicity comparison kernel simplicity structure]
read=->(p){File.file?(p) ? File.binread(p) : Zlib::GzipReader.open(p+'.gz', &:read)}
sha=->(p){Digest::SHA256.hexdigest(read.call(p))}
paths.each{|s,p|r=JSON.parse(read.call(p+'/RESULT.json'));abort 'Unverified scope' unless r['status']=='passed'&&r['mode']=='full'&&r['checkpoint']=="minus-orthogonal-rank-three-#{s}"}
r=JSON.parse(read.call(principal+'/RESULT.json'));abort 'Principal preservation not passed' unless r['status']=='passed'&&r['checkpoint']=='principal-constructions'
registry_path='docs/catalogue/catalogue.json';original=File.binread(registry_path);registry=JSON.parse(original)
base='verification/minus-orthogonal/rank-three';abort 'Evidence directory already exists' if File.exist?(base)
old=registry.fetch('evidence').fetch('minus-orthogonal-rank-two-supplement-v1')
entry=registry.fetch('entries').find{|e|e['id']=='family.2D'};abort 'Missing stable family' unless entry
exception=AtlasCatalogue::MINUS_RANK_THREE_EXCEPTIONS
ns='Atlas.Orthogonal.Minus.';dir='Atlas/LinearGroups/Orthogonal/Minus/'
props=[
 ['family_rankThree_comparison','AllRanks','Actual exterior-square/Hodge multiplicative equivalence with PSU4(q), in every characteristic'],
 ['family_order_all','AllRanks','Uniform projective order for every n>=2 over finite fields'],
 ['family_simple_all','AllRanks','Nonexceptional simplicity for every n>=2 over finite fields'],
 ['family_noncommutative_all','AllRanks','Noncommutativity for every n>=2 over finite fields'],
 ['family_elementary_perfect_all','AllRanks','Actual elementary group perfect for every n>=2'],
 ['rankThreeProjectiveHom_kernel','RankThreeKernel','Actual projective exterior-action kernel is exactly the SU4 center'],
 ['rankThreeElementaryHom_surjective','RankThreeFullImage','Actual SU4 exterior action surjects onto the elementary minus group']
].map{|n,f,d|{'declaration'=>ns+n,'source'=>dir+f+'.lean','description'=>d}}
entry['exceptions']=exception;entry['properties'].concat(props)
entry['presentation']['parameters']='Stable family n≥4; separately proved low ranks n=2,3; every finite field'
entry['presentation']['note']='Order and nonabelian simplicity proved uniformly for n≥2. Concrete low-rank comparisons: PSL₂(q²) and PSU₄(q). Stable principal roles and their independent evidence retain n≥4.'
key='minus-orthogonal-rank-three-supplement-v1';entry['evidence']=key
snapshot=JSON.parse(read.call(paths.fetch('structure')+'/SNAPSHOT.json'))
json=->(v){JSON.pretty_generate(v)+"\n"}
artifacts={'BASE_EVIDENCE.json'=>json.call(old),'ENTRY.json'=>json.call(entry),'RUNS.json'=>json.call(paths.transform_values{|p|{'directory'=>p,'manifest_sha256'=>sha.call(p+'/SHA256SUMS')}}),'RUN_PATHS.json'=>json.call(paths),'INVENTORY.json'=>json.call({'properties'=>props.map{|p|p.merge('entry'=>'Atlas.Orthogonal.Minus')},'exceptions'=>exception}),'THEOREM_STATEMENTS.txt'=>read.call(paths['structure']+'/statements.log'),'record-rank-three.rb'=>File.binread(__FILE__)}
FileUtils.mkdir_p(base);artifacts.each{|n,s|File.binwrite(base+'/'+n,s)}
manifest=artifacts.keys.sort.map{|n|"#{Digest::SHA256.file(base+'/'+n).hexdigest}  #{n}\n"}.join;File.write(base+'/MANIFEST.sha256',manifest)
evidence={'format'=>key,'directory'=>base,'manifest'=>base+'/MANIFEST.sha256','manifest_sha256'=>Digest::SHA256.hexdigest(manifest),'source_commit'=>snapshot['commit'],'toolchain'=>snapshot['toolchain'],'statements'=>base+'/THEOREM_STATEMENTS.txt'}
File.write(base+'/EVIDENCE.json',json.call(evidence))
AtlasCatalogue.shared_family_evidence(evidence,check_sources:true)
registry['evidence'].delete('minus-orthogonal-rank-two-supplement-v1');registry['evidence'][key]=evidence
registry['root_extension_evidence']={'directory'=>principal,'manifest_sha256'=>sha.call(principal+'/SHA256SUMS')}
registry['policy']['active_mathematical_job']='MINUS_ORTHOGONAL_FORMALIZATION_PROJECT.md — completed, including low-rank comparisons'
AtlasCatalogue.validate(registry,check_sources:true)
raise 'Registry changed during recording' unless File.binread(registry_path)==original
File.write(registry_path,json.call(registry));puts 'Recorded audited rank-three and all-ranks supplement; earlier evidence preserved.'
