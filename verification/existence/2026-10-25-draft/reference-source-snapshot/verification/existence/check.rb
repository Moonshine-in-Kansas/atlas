require_relative 'contracts'
rows=AtlasContracts.entries
raise 'Expected 34 contracts' unless rows.size==34
rows.each do |r|
 files=AtlasContracts.render(r)
 a,b=%w[Challenge.lean Solution.lean].map{|f|files.fetch(f).split(/^theorem /,2).last.split(':= by',2).first.strip}
 raise "Different statements: #{r['declaration']}" unless a==b
 raise 'Redundant noncommutativity in contract' if a.include?('¬ IsMulCommutative')
 raise 'Missing order/simplicity' unless a.include?('Nat.card G =') && a.include?('IsSimpleGroup G')
 raise 'Retain distinguishing invariant' if r['scope']=='discriminators' && !a.match?(/AtlasExistenceInvariant.k2|Subgroup.center/)
 raise 'Expected pending evidence' unless r['evidence'].include?('simplified_pending/')
end
puts 'PASS: 34 matched contracts; order, simplicity and four distinguishing invariants retained; no noncommutativity requirement.'
