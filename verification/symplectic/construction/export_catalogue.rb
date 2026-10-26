#!/usr/bin/env ruby
# Export maintained mathematical labels against actual, sealed compiled evidence.
# No theorem statement is reconstructed here: the compiler's full extraction is copied verbatim.
require 'json'
require 'digest'
require 'zlib'
require 'fileutils'
base=File.dirname(__FILE__)
run_paths={
  'order'=>'verification/runs/symplectic-order/20260914T065206-3',
  'simplicity'=>'verification/runs/symplectic-simplicity/20260914T065248-230',
  'exceptions'=>'verification/runs/symplectic-exceptions/20260914T064857-8',
  'structure'=>'verification/runs/symplectic-structure/20260914T065322-438'
}
read=lambda{|p|File.file?(p) ? File.binread(p) : Zlib::GzipReader.open(p+'.gz',&:read)}
run_paths.each_value do |p|
  result=JSON.parse(read.call(p+'/RESULT.json'))
  abort "Unaccepted run #{p}" unless result['status']=='passed'&&result['mode']=='full'
end
main=run_paths['structure']
snap=JSON.parse(read.call(main+'/SNAPSHOT.json'))
nodes=read.call(main+'/dependencies.jsonl').lines.map{|l|JSON.parse(l)}.to_h{|n|[n['name'],n]}
ref=lambda do |name|
  n=nodes.fetch(name)
  {'declaration'=>name,'source'=>n.fetch('module').tr('.','/')+'.lean'}
end
params='n is symplectic rank, dimension 2*n; F arbitrary finite field, q=|F|; simple exactly when (n=1 and q>3) or (n>=2 and (n,q)!=(2,2))'
formula='q^(n^2) * product_(i=1)^n (q^(2*i)-1) / gcd(2,q-1) (n>=1); order 1 at n=0'
roles={
  'model'=>ref.call('Atlas.Symplectic.PSp'),
  'finite'=>ref.call('Atlas.Symplectic.finite_psp'),
  'order'=>ref.call('Atlas.Symplectic.card_psp').merge('formula'=>formula),
  'simple'=>ref.call('Atlas.Symplectic.simple_of_good'),
  'nonabelian'=>ref.call('Atlas.Symplectic.projective_not_commutative')
}
properties={
  'Atlas.Symplectic.card_sp'=>'Uniform full matrix-group order, including rank zero',
  'Atlas.Symplectic.card_center'=>'Square-one scalar center cardinality',
  'Atlas.Symplectic.mem_center_iff_scalar'=>'Exact scalar center identification',
  'Atlas.Symplectic.center_mul_card_psp'=>'Division-free positive-rank quotient order',
  'Atlas.Symplectic.center_order_dvd'=>'Exact numerator divisibility',
  'Atlas.Symplectic.center_denominator_positive'=>'Positive denominator',
  'Atlas.Symplectic.simple_iff_good'=>'Exact simplicity range including all failures',
  'Atlas.Symplectic.projection_kernel'=>'Actual central quotient kernel',
  'Atlas.Symplectic.projection_surjective'=>'Surjective canonical quotient',
  'Atlas.Symplectic.exists_isometry'=>'Transport of every nondegenerate alternating form of dimension 2*n',
  'Atlas.Symplectic.fullLinearIsometryEquiv_action'=>'Full linear-isometry multiplicative comparison respects the actual action',
  'Atlas.Symplectic.transvectionGroup_eq_top'=>'Full symplectic transvection generation in every characteristic',
  'Atlas.Symplectic.projectiveTransvectionGroup_eq_top'=>'Full projective transvection generation',
  'Atlas.Symplectic.projective_faithful'=>'Faithful natural projective action',
  'Atlas.Symplectic.pointPerm_kernel'=>'Exact projective action kernel upstairs',
  'Atlas.Symplectic.stabilizer_orbit_iff'=>'Actual rank-three point-stabilizer orbits for rank at least two',
  'Atlas.Symplectic.projective_preprimitive'=>'Projective primitivity for rank at least two, including the binary exception',
  'Atlas.Symplectic.card_points'=>'Projective point count',
  'Atlas.Symplectic.card_suborbit_one'=>'Orthogonal nontrivial subdegree',
  'Atlas.Symplectic.card_suborbit_two_power'=>'Nonorthogonal subdegree',
  'Atlas.Symplectic.perfect_of_good'=>'Perfectness upstairs, including the binary and ternary branches',
  'Atlas.Symplectic.projective_perfect_of_good'=>'Perfectness of the actual quotient',
  'Atlas.Symplectic.card_lineTransvections'=>'Line-transvection subgroup order q',
  'Atlas.Symplectic.lineTransvections_normal'=>'Normality in the actual point stabilizer',
  'Atlas.Symplectic.toPGL_injective'=>'Embedding of the actual quotient in the retained PGL model',
  'Atlas.Symplectic.toPGL_action'=>'PGL embedding respects projective action',
  'Atlas.Symplectic.rankOnePSL_projection'=>'Rank-one comparison respects the quotient maps',
  'Atlas.Symplectic.rankOneSL_action'=>'Rank-one SL comparison respects the natural linear action',
  'Atlas.Symplectic.rankOnePSL_action'=>'Rank-one PSL comparison respects projective action',
  'Atlas.Symplectic.exceptionalNormal_card'=>'Actual binary rank-two normal subgroup has order 360',
  'Atlas.typeC_construction'=>'Public construction package for the actual Sp and PSp models',
  'Atlas.exists_typeC'=>'Existence witnessed by the actual constructed quotient',
  'Atlas.typeC_prime_power'=>'Actual finite-field realization for prime p and exponent f>=1',
  'Atlas.Symplectic.Checks.galois_four'=>'Actual field-of-order-four regression'
}.map{|n,d|ref.call(n).merge('description'=>d)}
entry={
  'id'=>'family.C','label'=>'C_n(q) / PSp(2n,q)','kind'=>'family','audit_entry'=>'C',
  'proof_status'=>'construction_complete',
  'construction'=>'Carrier of Matrix.symplecticGroup (Fin n) F, quotiented by its actual center',
  'parameters'=>params,'exceptions'=>'Rank zero is trivial; nonsimple positive-rank pairs (n,q)=(1,2),(1,3),(2,2)',
  'recognition'=>'Constructed symplectic family with its natural alternating form and actions; no CFSG or external recognition theorem assumed',
  'attribution'=>'mathlib matrix carrier, finite-field and projective APIs, Iwasawa criterion and rank-one PSL simplicity; ATLAS hyperbolic splitting/counting, full generation, small-field perfectness, geometry, center and binary exception',
  'owner'=>'Gerald Höhn','upstream_status'=>'No upstream acceptance claimed',
  'roles'=>roles,'properties'=>properties,'evidence'=>'symplectic-family-f07f142'
}
row={'entry'=>'C','kind'=>'family','checking'=>'checked: independent full order, positive-simplicity, exception and structural audits',
 'parameters'=>params,'order'=>formula,'model'=>roles['model']['declaration'],'finiteness_theorem'=>roles['finite']['declaration'],
 'order_theorem'=>roles['order']['declaration'],'simplicity_theorem'=>roles['simple']['declaration'],
 'noncommutativity'=>roles['nonabelian']['declaration']}
inventory={'groups'=>[row],'properties'=>properties.map{|p|p.merge('entry'=>'Atlas.Symplectic')},
 'catalogue_scope'=>entry.slice('id','label','kind','audit_entry','proof_status','construction','parameters','exceptions')}
File.write(base+'/ENTRY.json',JSON.pretty_generate(entry)+"\n")
File.write(base+'/INVENTORY.json',JSON.pretty_generate(inventory)+"\n")
File.write(base+'/RUNS.json',JSON.pretty_generate(run_paths.transform_values{|p|{'directory'=>p,'manifest_sha256'=>Digest::SHA256.file(p+'/SHA256SUMS').hexdigest}})+"\n")
statements=read.call(main+'/statements.log')
File.binwrite(base+'/THEOREM_STATEMENTS.txt',statements)
Zlib::GzipWriter.open(base+'/THEOREM_STATEMENTS.txt.gz'){|g|g.mtime=0;g.write(statements)}
files=%w[ENTRY.json INVENTORY.json RUNS.json THEOREM_STATEMENTS.txt THEOREM_STATEMENTS.txt.gz]
File.write(base+'/MANIFEST.sha256',files.map{|n|"#{Digest::SHA256.file(base+'/'+n).hexdigest}  #{n}\n"}.join)
evidence={'format'=>'shared-family-v1','directory'=>base,'manifest'=>base+'/MANIFEST.sha256',
 'manifest_sha256'=>Digest::SHA256.file(base+'/MANIFEST.sha256').hexdigest,
 'source_commit'=>snap['commit'],'toolchain'=>snap['toolchain'],'statements'=>base+'/THEOREM_STATEMENTS.txt.gz'}
File.write(base+'/EVIDENCE.json',JSON.pretty_generate(evidence)+"\n")
puts "Prepared one symplectic family inventory, #{properties.size} audited public properties; actual statements copied verbatim."
