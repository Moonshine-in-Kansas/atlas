require 'json'
d=__dir__;inv=File.readlines("#{d}/inventory.log").filter_map{|l|l.split("ATLAS_DECL\t",2)[1]&.strip&.split("\t")}
r=inv.select{|n,m,k|k=='theorem'&&n.match?(/\AAtlas\.Sporadic\.Fischer24\.[^.]+\z/)}.map(&:first)
File.write("#{d}/aux.json",JSON.pretty_generate(r))
s=File.read("#{d}/Extract.lean");s.sub!(/  let roots := .*\n/,"  let roots := #["+r.map{|n|"``#{n}"}.join(', ')+"]\n");s.sub!('nodes.jsonl','aux-nodes.jsonl');File.write("#{d}/Auxiliary.lean",s)
