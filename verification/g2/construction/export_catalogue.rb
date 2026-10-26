#!/usr/bin/env ruby
# Bind one concrete family to separate full compiled evidence; copy statements verbatim.
require 'json'
require 'digest'
require 'zlib'
base=File.dirname(__FILE__)
run_paths=JSON.parse(File.read(base+'/RUN_PATHS.json'))
abort 'Expected four separate scopes' unless run_paths.keys.sort==%w[exceptions order simplicity structure]
read=lambda{|p|File.file?(p) ? File.binread(p) : Zlib::GzipReader.open(p+'.gz',&:read)}
run_paths.each_value do |p|
  r=JSON.parse(read.call(p+'/RESULT.json'))
  abort "Unaccepted run #{p}" unless r['status']=='passed'&&r['mode']=='full'
end
main=run_paths.fetch('structure')
snap=JSON.parse(read.call(main+'/SNAPSHOT.json'))
nodes=read.call(main+'/dependencies.jsonl').lines.map{|l|JSON.parse(l)}.to_h{|n|[n.fetch('name'),n]}
ref=lambda{|n|r=nodes.fetch(n);{'declaration'=>n,'source'=>r.fetch('module').tr('.','/')+'.lean'}}
params='F is an arbitrary finite field, q=|F|, including characteristics 2 and 3; simple exactly when q>2'
formula='q^6 * (q^6-1) * (q^2-1)'
roles={
  'model'=>ref.call('Atlas.G2.Model'),
  'finite'=>ref.call('Atlas.G2.finite_model'),
  'order'=>ref.call('Atlas.G2.card_Model').merge('formula'=>formula),
  'simple'=>ref.call('Atlas.G2.isSimple'),
  'nonabelian'=>ref.call('Atlas.G2.exists_mul_ne_mul')
}
properties={
 'Atlas.G2.isSimple_iff'=>'Exact simplicity range for the same full octonion automorphism model',
 'Atlas.G2.singularPoints_primitive'=>'Actual singular-point action is primitive, including q=2',
 'Atlas.G2.singularPointsFaithful'=>'Faithful singular-point action independent of simplicity',
 'Atlas.G2.card_singularPoints'=>'Uniform singular-point count (q^6-1)/(q-1)',
 'Atlas.G2.card_orbitClass'=>'Actual point-stabilizer subdegrees 1,q(q+1),q^3(q+1),q^5',
 'Atlas.G2.parabolic_eq_pointStabilizer'=>'Displayed Borel and Weyl map generate the full point stabilizer',
 'Atlas.G2.parabolicNormalForm'=>'Explicit stabilizer parameter bijection F-units times F^5 times SL2(F)',
 'Atlas.G2.borel_relIndex_parabolic'=>'Borel has index q+1 in the actual point stabilizer',
 'Atlas.G2.generated_eq_top'=>'Explicit Dickson/Wilson maps generate the full automorphism group',
 'Atlas.G2.card_unipotent'=>'Unique six-parameter unipotent normal form has order q^6',
 'Atlas.G2.card_borel'=>'Actual Borel order q^6(q-1)^2',
 'Atlas.G2.localAt_eq_of_transport'=>'Local group is independent of the chosen point transporter',
 'Atlas.G2.localAt_conj'=>'Covariant conjugate family of actual local groups',
 'Atlas.G2.card_localAt'=>'Each canonical local group has order q^2',
 'Atlas.G2.localAt_normal'=>'Local group is normal in the actual corresponding point stabilizer',
 'Atlas.G2.iwasawa'=>'Actual IwasawaStructure for every q>2',
 'Atlas.G2.isPerfect'=>'Uniform torus-commutator perfectness for q>2, including q=3',
 'Atlas.G2.card_longRootNormalClosure_binary'=>'Actual long-root normal closure has order6048 when q=2',
 'Atlas.G2.index_longRootNormalClosure_binary'=>'Actual long-root normal closure has index2 when q=2',
 'Atlas.G2.not_simple_binary'=>'Genuine nonsimplicity of the same model at q=2',
 'Atlas.G2.fieldEquiv'=>'Actual group transport under arbitrary field isomorphisms',
 'Atlas.G2.longRootNormalClosureFieldEquiv'=>'Field transport preserves the actual exception subgroup',
 'Atlas.typeG2_construction'=>'Complete public construction package for the concrete octonion automorphism family',
 'Atlas.exists_typeG2'=>'Simple-group existence witnessed by the actual octonion model',
 'Atlas.typeG2_prime_power'=>'Finite-field realization for every prime p and exponent f>=1',
 'Atlas.exists_typeG2_prime_power'=>'Simple noncommutative existence for prime p, exponent f>=1 and p^f>2',
 'Atlas.G2.OrderChecks.four_order'=>'Uniform-order specialization over an actual field of order4',
 'Atlas.G2.SimplicityChecks.four_simple'=>'Simplicity over an actual field of order4'
}.filter_map{|n,d| next unless nodes.fetch(n)['kind']=='theorem'; ref.call(n).merge('description'=>d)}
entry={
 'id'=>'family.G2','label'=>'G2(q)','kind'=>'family','audit_entry'=>'G2',
 'proof_status'=>'construction_complete',
 'construction'=>'Full group of linear multiplication-preserving automorphisms of the uniform eight-coordinate split octonion algebra',
 'parameters'=>params,'exceptions'=>'q=2: actual long-root normal closure has order6048 and index2 in G2(2), whose order is12096',
 'recognition'=>'Concrete Dickson/Wilson octonion construction; no general Chevalley, CFSG, order-recognition or PSU3(3) comparison theorem assumed',
 'attribution'=>'ATLAS split-octonion table, explicit root maps and coordinate stabilizer geometry; pinned mathlib finite-field, SL2 and Iwasawa infrastructure',
 'owner'=>'Gerald Höhn','upstream_status'=>'No upstream acceptance claimed',
 'roles'=>roles,'properties'=>properties,'evidence'=>'g2-octonion-family-v1'
}
row={'entry'=>'G2','kind'=>'family','checking'=>'checked: separate full structure, order, positive-simplicity and binary-exception audits',
 'parameters'=>params,'order'=>formula,'model'=>roles['model']['declaration'],'finiteness_theorem'=>roles['finite']['declaration'],
 'order_theorem'=>roles['order']['declaration'],'simplicity_theorem'=>roles['simple']['declaration'],
 'noncommutativity'=>roles['nonabelian']['declaration']}
inventory={'groups'=>[row],'properties'=>properties.map{|p|p.merge('entry'=>'Atlas.G2')},
 'catalogue_scope'=>entry.slice('id','label','kind','audit_entry','proof_status','construction','parameters','exceptions')}
File.write(base+'/ENTRY.json',JSON.pretty_generate(entry)+"\n")
File.write(base+'/INVENTORY.json',JSON.pretty_generate(inventory)+"\n")
File.write(base+'/RUNS.json',JSON.pretty_generate(run_paths.transform_values{|p|{'directory'=>p,'manifest_sha256'=>Digest::SHA256.file(p+'/SHA256SUMS').hexdigest}})+"\n")
statements=read.call(main+'/statements.log')
File.binwrite(base+'/THEOREM_STATEMENTS.txt',statements)
Zlib::GzipWriter.open(base+'/THEOREM_STATEMENTS.txt.gz'){|g|g.mtime=0;g.write(statements)}
files=%w[ENTRY.json INVENTORY.json RUNS.json THEOREM_STATEMENTS.txt THEOREM_STATEMENTS.txt.gz]
File.write(base+'/MANIFEST.sha256',files.map{|n|"#{Digest::SHA256.file(base+'/'+n).hexdigest}  #{n}\n"}.join)
evidence={'format'=>'g2-family-v1','directory'=>base,'manifest'=>base+'/MANIFEST.sha256',
 'manifest_sha256'=>Digest::SHA256.file(base+'/MANIFEST.sha256').hexdigest,
 'source_commit'=>snap['commit'],'toolchain'=>snap['toolchain'],'statements'=>base+'/THEOREM_STATEMENTS.txt.gz'}
File.write(base+'/EVIDENCE.json',JSON.pretty_generate(evidence)+"\n")
puts "Prepared one G2 family and #{properties.size} audited properties; copied actual compiled statements."
