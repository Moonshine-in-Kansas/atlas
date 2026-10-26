require 'json'; require 'csv'; require 'set'; require 'digest'
d=__dir__; snap=JSON.parse(File.read("#{d}/SNAPSHOT.json"))
roots=JSON.parse(File.read("#{d}/roots.json")); selected=(JSON.parse(File.read("#{d}/selected.json"))+JSON.parse(File.read("#{d}/extra.json"))+JSON.parse(File.read("#{d}/aux.json"))).uniq
nodes={}; %w[nodes.jsonl extra-nodes.jsonl aux-nodes.jsonl].each{|f|File.foreach("#{d}/#{f}"){|l|j=JSON.parse(l);nodes[j['name']]=j}}
range_modules=File.readlines("#{d}/range-modules.tsv").to_h{|l|l.strip.split("\t",2)}
nodes.each_value{|j|j["source_module"]=range_modules[j["range_parent"]]}
missing=nodes.values.flat_map{|n|n['dependencies']}.uniq-nodes.keys;abort "Missing nodes #{missing}" unless missing.empty?
File.write("#{d}/DEPENDENCIES.json",JSON.generate({snapshot:snap['commit'],edge_convention:'declaration -> constants referenced; type and value labelled separately; dependencies union includes inductive/recursor metadata',roots:roots,selected:selected,nodes:nodes.values}))
def closure(nodes,root)
 seen=Set.new;work=[root];until work.empty?;n=work.pop;next unless seen.add?(n);work.concat(nodes.fetch(n)['dependencies']);end;seen
end
closures=selected.to_h{|r|[r,closure(nodes,r)]}
File.write("#{d}/AXIOMS.txt",(%w[extract.log extra.log aux.log].flat_map{|p|File.readlines("#{d}/#{p}").grep(/^AXIOMS /)}).join)
File.write("#{d}/THEOREM_STATEMENTS.txt",%w[extract.log extra.log aux.log definitions.log].map{|f|"\n===== #{f} =====\n"+File.read("#{d}/#{f}")}.join)
File.write("#{d}/TRUST.json",JSON.pretty_generate({nodes:nodes.size,selected:selected.size,missing:missing,axioms:nodes.values.select{|n|n['kind']=='axiom'}.map{|n|n['name']}.sort,suspicious:nodes.keys.grep(/sorryAx|ofReduceBool|ofReduceNat|native_decide|Lean\.trust|axiom/i),principal_axioms:roots.to_h{|r|[r,closures[r].select{|n|nodes[n]['kind']=='axiom'}.sort]}}))
# Ranges are line intervals, not imported-file sizes. Generated nested declarations use parent range.
missing_ranges=[]
line_ids={};nextid=0; spanids={}
nodes.each do |name,j|
 mod=j['source_module'];sp=j['span'];next if sp.nil? || mod.nil?
 if mod.start_with?('Atlas.')
 path=mod.tr('.','/')+'.lean'
 else
 path=mod.tr('.','/')+'.lean'
 end
 last=sp[1]-(sp[2]==0 ? 1:0);ids=[]
 (sp[0]..last).each{|l| key=[path,l];line_ids[key] ||= (nextid+=1);ids<<line_ids[key]}
 spanids[name]=ids
end
def footprint(nodes,closure,spanids,atlas)
 out=Set.new; closure.each{|n|next unless (nodes[n]['source_module'] || nodes[n]['module']).start_with?('Atlas.')==atlas; out.merge(spanids.fetch(n,[]))};out
end
rows=[];global=Set.new;globalext=Set.new
roots.each_slice(2) do |o,s|
 oc=closures[o];sc=closures[s];a=footprint(nodes,oc,spanids,true);b=footprint(nodes,sc,spanids,true);ea=footprint(nodes,oc,spanids,false);eb=footprint(nodes,sc,spanids,false);u=a|b;global.merge(u);globalext.merge(ea|eb)
 name=o.sub(/\.card(_factorial)?$/,'');name='PSL' if o=='Atlas.card_psl_factor'
 rows<<[name,o,s,a.size,b.size,(a&b).size,u.size,ea.size,eb.size,(ea|eb).size]
 (oc|sc).each{|n|missing_ranges<<[name,n,nodes[n]['module']] unless spanids.key?(n)}
end
CSV.open("#{d}/CODE_COUNTS.csv",'w'){|c|c<<%w[entry order_root simplicity_root atlas_order_lines atlas_simplicity_lines atlas_overlap_lines atlas_union_lines external_order_lines external_simplicity_lines external_union_lines];rows.each{|r|c<<r};c<<['GLOBAL_UNION','','','','','',global.size,'','',globalext.size]}
CSV.open("#{d}/MISSING_RANGES.csv",'w'){|c|c<<%w[entry declaration module];missing_ranges.each{|r|c<<r}}
# Root closure project dependencies for readable review, including cross-group links.
CSV.open("#{d}/CROSS_GROUP_DEPENDENCIES.csv",'w'){|c|c<<%w[root referenced_declaration module];roots.each{|r|closures[r].sort.each{|n|j=nodes[n];c<<[r,n,j['module']] if j['module'].start_with?('Atlas.') && n.match?(/(simple|[Oo]rder|[Rr]ecognition|[Cc]lassification|[Cc]ard)/)}}}
CSV.open("#{d}/EXTERNAL_THEOREMS.csv",'w'){|c|c<<%w[declaration module];all=roots.flat_map{|r|closures[r].to_a}.uniq;all.sort.each{|n|j=nodes[n];c<<[n,j['module']] if j['kind']=='theorem'&&!j['module'].start_with?('Atlas.')}}
inv=File.readlines("#{d}/inventory.log").filter_map{|l|l.split("ATLAS_DECL\t",2)[1]&.strip&.split("\t")};mods=inv.map{|n,m,k|m}.uniq
CSV.open("#{d}/SOURCE_COVERAGE.csv",'w'){|c|c<<%w[path lines tracked imported_public_declarations];snap['sources'].each{|p,j|c<<[p,j['lines'],j['tracked'],mods.include?(p.delete_suffix('.lean').tr('/','.'))]}}
counts={core_all:snap['sources'].values.sum{|j|j['lines']},core_tracked:snap['sources'].values.select{|j|j['tracked']}.sum{|j|j['lines']},core_untracked:snap['sources'].values.reject{|j|j['tracked']}.sum{|j|j['lines']},core_files:snap['sources'].size,root_audit_lines:snap['sources'].fetch('Atlas/Audit.lean')['lines'],external_sources:{},principal_atlas_union:global.size,principal_external_union:globalext.size,missing_atlas_ranges:missing_ranges.count{|_,_,m|m.start_with?('Atlas.')},missing_external_ranges:missing_ranges.count{|_,_,m|!m.start_with?('Atlas.')}}
Dir.glob('.lake/packages/*').select{|p|File.directory?(p)}.each{|p|fs=Dir.glob("#{p}/**/*.lean").reject{|f|f.include?('/.lake/')&& !f.start_with?(p+'/')};counts[:external_sources][p]={files:fs.size,lines:fs.sum{|f|File.foreach(f).count}}}
File.write("#{d}/COUNTS.json",JSON.pretty_generate(counts))
CSV.open("#{d}/PROPERTIES.csv",'w'){|c|c<<%w[entry declaration source category exact_statement assumptions checking dependency_closure_size alias_policy];selected.each{|r|j=nodes[r];kind=r.split('.').last;c<<[r.split('.')[0...-1].join('.'),r,j['module'].tr('.','/')+'.lean',kind,'THEOREM_STATEMENTS.txt: STATEMENT '+r,'Full parameters/instances in exact statement; not replaced by axiom list','checked: current build and compiled extraction',closures[r].size,'Inventory includes public aliases; do not count rows as independent mathematics']}}
changed=snap['sources'].keys.select{|p|Digest::SHA256.file(p).hexdigest!=snap['sources'][p]['sha256']};abort "SOURCE CHANGED #{changed}" unless changed.empty?
puts counts.to_json
