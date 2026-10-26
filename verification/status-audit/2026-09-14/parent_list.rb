require 'json'
d=__dir__;names=[]
%w[nodes.jsonl extra-nodes.jsonl aux-nodes.jsonl].each{|p|File.foreach("#{d}/#{p}"){|l|j=JSON.parse(l);names<<j['range_parent'] if j['span']}}
File.write("#{d}/range-parents.txt",names.uniq.join("\n"))
