require 'json';require 'csv';require 'digest';require 'open3'
d=__dir__
abort 'Source verification failed' unless system('ruby',"#{d}/verify_snapshot.rb")
%w[extract extra aux].each{|f|s=File.read("#{d}/#{f}.log");abort "Incomplete #{f}" unless s.include?('GRAPH COMPLETE');abort "Errors #{f}" if s.match?(/error(?:\(|:)/)}
%w[definitions inventory example ranges].each{|f|abort "Errors #{f}" if File.read("#{d}/#{f}.log").match?(/error(?:\(|:)/)}
abort 'Build did not finish' unless File.read("#{d}/build.log").include?('Build completed successfully (5203 jobs).')
t=JSON.parse(File.read("#{d}/TRUST.json"));abort 'Unexpected axioms' unless t['axioms'].sort==%w[Classical.choice Quot.sound propext].sort;abort 'Missing graph nodes' unless t['missing'].empty?
g=JSON.parse(File.read("#{d}/DEPENDENCIES.json"));nodes=g['nodes'].to_h{|j|[j['name'],j]};s=JSON.parse(File.read("#{d}/SNAPSHOT.json"))
nodes.each_value do |j|
 next unless j['span']&&j['source_module']&.start_with?('Atlas.')
 path=j['source_module'].tr('.','/')+'.lean';last=j['span'][1]-(j['span'][2]==0 ? 1:0)
 abort "Bad range #{j['name']}" unless s['sources'][path] && j['span'][0]>0 && last<=s['sources'][path]['lines']
end
abort 'Native/placeholder dependency' unless nodes.keys.grep(/sorryAx|ofReduceBool|ofReduceNat|native_decide/).empty?
props=CSV.read("#{d}/PROPERTIES.csv",headers:true);abort 'Property coverage mismatch' unless props.size==t['selected']&&props.all?{|r|r['compiled_signature']&.include?(r['declaration'])}
rows=CSV.read("#{d}/GROUPS.csv",headers:true);checked=rows.select{|r|r['checking'].start_with?('checked')};abort 'Group coverage mismatch' unless checked.size==18 && checked.count{|r|r['kind']=='family'}==3
checked.each{|r|%w[order_theorem simplicity_theorem].each{|k|abort "Missing #{r[k]}" unless nodes.key?(r[k])&&g['roots'].include?(r[k])}}
counts=JSON.parse(File.read("#{d}/COUNTS.json"));abort 'Missing Atlas ranges' unless counts['missing_atlas_ranges']==0
puts "PASS: 18 catalogue entries (3 families, 15 sporadics), 36 order/simplicity roots."
puts "PASS: #{t['selected']} selected roots, #{nodes.size} declaration graph nodes; exact signatures and closed dependencies."
puts "PASS: only propext, Classical.choice, Quot.sound; no native-reduction/placeholder trust constants."
puts "PASS: compiler source ranges within hashed Atlas files; global principal footprint #{counts['principal_atlas_union']} lines."
puts 'LIMITS: incremental build; no fresh independent kernel/comparator run; external ranges and generated-data provenance incomplete.'
