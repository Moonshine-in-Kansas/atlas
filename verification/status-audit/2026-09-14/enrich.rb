require 'csv';require 'json'
d=__dir__
text=%w[extract.log extra.log aux.log].map{|p|File.read("#{d}/#{p}")}.join("\n")
sigs={};text.scan(/^STATEMENT ([\w.]+)\n(.*?)^AXIOMS \1: [^\n]*$/m){|n,s|sigs[n]=s.strip}
t=CSV.read("#{d}/PROPERTIES.csv",headers:true)
CSV.open("#{d}/PROPERTIES.csv",'w'){|c|h=t.headers.reject{|x|x=='compiled_signature'};c<<(h+['compiled_signature']);t.each{|r|c<<(h.map{|x|r[x]}+[sigs.fetch(r['declaration'])])}}
t=CSV.read("#{d}/GROUPS.csv",headers:true)
CSV.open("#{d}/GROUPS.csv",'w') do |c|
 h=t.headers.reject{|x|%w[group_structure_evidence model_definition_evidence].include?(x)};c<<(h+['group_structure_evidence','model_definition_evidence'])
 t.each do |r|
   checked=r['checking'].start_with?('checked')
   c<<(h.map{|x|r[x]}+[checked ? "Explicit Group argument in compiled #{r['simplicity_theorem']} (THEOREM_STATEMENTS.txt); its subgroup/quotient/transport instance dependencies are in DEPENDENCIES.json" : 'missing',checked ? 'definitions.log: printed model and recursively reached project definitions with instances' : 'missing'])
 end
end
File.write("#{d}/EXAMPLE.txt",File.readlines("#{d}/example.log").reject{|l|l.start_with?('IMPORTED_MODULE ')}.join)
# Keep auxiliary central forms separate; these do not add simple entries.
CSV.open("#{d}/AUXILIARY_GROUPS.csv",'a') do |f|
 f<<['3.Fi24Prime','actual positive linear cover',3765617127571985163878400,'Atlas.Sporadic.Fischer24.linear_card','checked: selected compiled signature and full dependency graph']
 f<<['full Fischer semilinear group','full semilinear algebra group; scalar C3 not central in the full extension',7531234255143970327756800,'Atlas.Sporadic.Fischer24.algebra_card','checked: selected compiled signature and full dependency graph']
 f<<['2.Fi22','actual double centralizer extension',129123503308800,'Atlas.Fischer.DoubleCover22.card','root-imported current build; separate historical certificate not rerun/extracted in this audit']
end
