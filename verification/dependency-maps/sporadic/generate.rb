#!/usr/bin/env ruby
require 'json'
require 'set'
require 'digest'
require 'cgi'
require 'erb'
require 'open3'
require 'fileutils'
require 'zlib'
ROOT=File.expand_path('../../..',__dir__)
Dir.chdir(ROOT)
PUBLIC=File.file?('catalogue/catalogue.json')
AUDIT=PUBLIC ? 'verification/release' : 'verification/runs/principal-constructions/20260928T100308-655895'
CATALOGUE=JSON.parse(File.read(PUBLIC ? 'catalogue/catalogue.json' : 'release/catalogue/catalogue.json'))
ENTRIES=CATALOGUE.fetch('entries').select{|e|e['kind']=='sporadic'}.to_h{|e|[e.fetch('id').delete_prefix('sporadic.'),e]}
GROUPS=%w[M24 M23 M22 M12 M11]+(ENTRIES.keys-%w[M24 M23 M22 M12 M11])
LABELS=ENTRIES.transform_values{|e|e.dig('presentation','label')||e.fetch('label')}
nodes={}
reader=File.file?(AUDIT+'/dependencies.jsonl') ? File.open(AUDIT+'/dependencies.jsonl') : Zlib::GzipReader.open(AUDIT+'/dependencies.jsonl.gz')
reader.each_line do |line|
 j=JSON.parse(line)
 nodes[j['name']]=j if j['module']&.start_with?('Atlas.') || j['source_module']&.start_with?('Atlas.')
end
reader.close
snapshot=PUBLIC ? {'source_hashes'=>JSON.parse(File.read(AUDIT+'/SOURCE_HASHES.json')),'commit'=>nil} : JSON.parse(File.read(AUDIT+'/SNAPSHOT.json'))
audit_link=PUBLIC ? AUDIT+'/RESULT.json' : AUDIT+'/CERTIFICATE.md'
audit_date=JSON.parse(File.read(AUDIT+'/RESULT.json')).fetch(PUBLIC ? 'started_utc' : 'started_utc')[0,10]
current_hashes=PUBLIC ? JSON.parse(File.read(JSON.parse(File.read('verification/current.json')).fetch('snapshot')+'/SOURCE_HASHES.json')) : snapshot['source_hashes']
raise 'Audit is not a pass' unless JSON.parse(File.read(AUDIT+'/RESULT.json'))['status']=='passed'
source=->(n){(nodes.fetch(n)['source_module']||nodes[n]['module']).tr('.','/')+'.lean'}
roots=GROUPS.to_h{|g|[g,{'order'=>ENTRIES[g].dig('roles','order','declaration'),'simplicity'=>ENTRIES[g].dig('roles','simple','declaration')}]}
full={}
GROUPS.each do |g|
 full[g]=roots[g].transform_values do |root|
  seen=Set.new;todo=[root]
  until todo.empty?
   n=todo.pop;next unless seen.add?(n)
   raise "Missing root #{n}" unless nodes[n]
   todo.concat(nodes[n]['dependencies'].select{|d|nodes[d]})
  end
  seen
 end
end
# Explicit presentation boundaries: no claim that a whole other group package is needed.
# Its exact reached declarations are recorded below; traversal stops at each boundary.
m24base=full['M24'].values.reduce(:|).map{|n|source.call(n)}.to_set
co1base=full['Co1'].values.reduce(:|).map{|n|source.call(n)}.to_set
fischerbase=full['Fi24Prime'].values.reduce(:|).map{|n|source.call(n)}.to_set
public_names={'Mathieu11'=>'M11','Mathieu12'=>'M12','Mathieu22'=>'M22','Mathieu23'=>'M23','Mathieu24'=>'M24',
 'Conway1'=>'Co1','Conway2'=>'Co2','Conway3'=>'Co3','McLaughlin'=>'McL','HigmanSims'=>'HS',
 'Suzuki'=>'Suz','Janko2'=>'J2','Fischer22'=>'Fi22','Fischer23'=>'Fi23','Fischer24Prime'=>'Fi24Prime'}
owner=->(n) do
 p=source.call(n);base=File.basename(p,'.lean')
 public_name=public_names.keys.find{|prefix|base.start_with?(prefix)} if p.start_with?('Atlas/Sporadic/')
 if public_name
  public_names[public_name]
 elsif p.match(%r{/(?:Mathieu|TernaryMathieu)(11|12|22|23|24)[^/]*\.lean$})
  "M#{$1}"
 elsif base.start_with?('Dodecad')
  'M12'
 elsif base.start_with?('Co2')
  'Co2'
 elsif base.start_with?('Co3','NormSix')
  'Co3'
 elsif base.start_with?('McL')
  'McL'
 elsif base.start_with?('HS')
  'HS'
 elsif base.start_with?('Eisenstein')
  'Suz'
 elsif base.start_with?('Icosian')
  'J2'
 elsif p.start_with?('Atlas/Conway/') && (base.start_with?('Quotient','DerivedCross','LeechCentralQuotient','LeechQuotient','LeechCrossKernel','MonomialCentralQuotient')||base=='ConwaySimplicity')
  'Co1'
 elsif p.start_with?('Atlas/Conway/') && (base.start_with?('OrthogonalLine','OrthogonalMinimumLines','Antipodal','ShortenedGolay','Co2')||base=='MinimumVectorStabilizer'||base=='GolayPairSetSemidirect')
  'Co2'
 elsif p.start_with?('Atlas/Fischer/') && fischerbase.include?(p)
  'Shared Fischer tensor / ray construction'
 elsif p.start_with?('Atlas/Lattices/Leech')
  'Shared Leech lattice'
 elsif p.start_with?('Atlas/Conway/') && co1base.include?(p)
  'Co0 / Leech isometries'
 elsif p.start_with?('Atlas/Codes/')
  'Shared Golay / hexacode'
 elsif m24base.include?(p)&&!p.start_with?('Atlas/GroupTheory/')&&!p.start_with?('Atlas/Families/')
  'Shared Golay / M24 geometry'
 else
  nil
 end
end
# Source-command count: strip nested comments and string contents before scanning.
def clean_lean(s)
 o='';i=0;depth=0;str=false
 while i<s.length
  pair=s[i,2];c=s[i]
  if depth>0
   if pair=='/-';depth+=1;i+=2;o<<'  ';next
   elsif pair=='-/';depth-=1;i+=2;o<<'  ';next;end
   o<<(c=="\n" ? "\n" : ' ');i+=1
  elsif str
   if c=='\\';o<<'  ';i+=2
   else;str=false if c=='"';o<<(c=="\n" ? "\n" : ' ');i+=1;end
  elsif pair=='/-';depth=1;i+=2;o<<'  '
  elsif pair=='--';j=s.index("\n",i)||s.length;o<<' '*(j-i);i=j
  elsif c=='"';str=true;o<<' ';i+=1
  else;o<<c;i+=1;end
 end
 o
end
cache={}
allfiles=full.values.flat_map{|scopes|scopes.values.flat_map{|ns|ns.map{|n|source.call(n)}}}.uniq
allfiles.each do |p|
 hash=Digest::SHA256.file(p).hexdigest
 raise "Source changed since current evidence: #{p}" unless current_hashes[p]==hash
 unless snapshot['source_hashes'][p]==hash
  historical=File.read(p).sub('Released under the ATLAS Research and Attribution License 1.0; see LICENSE.',
    'Released under Apache 2.0 license as described in the file LICENSE.')
  raise "Change beyond the release licence header: #{p}" unless PUBLIC && Digest::SHA256.hexdigest(historical)==snapshot['source_hashes'][p]
 end
 named=clean_lean(File.read(p)).scan(/\b(?:theorem|lemma)\s+(«[^»]+»|[\p{L}_][\p{L}\p{N}_'.!?]*)/u).flatten
 cache[p]={'total'=>named.size,'sha256'=>hash}
end
commit=Open3.capture2('git','rev-parse','HEAD').first.strip
summaries=[]
GROUPS.each do |g|
 boundary=->(n) do
  own=owner.call(n)
  # M24 expands the original construction; descendants reuse it as a boundary.
  expanded=(g=='M24'&&own&.start_with?('Shared')) ||
   (g=='Co1'&&['Shared Leech lattice','Co0 / Leech isometries'].include?(own)) ||
   (g=='Fi24Prime'&&own=='Shared Fischer tensor / ray construction')
  own && own!=g && !expanded ? own : nil
 end
 local={}; external={}
 roots[g].each do |role,root|
  seen=Set.new;stop=Set.new;todo=[root]
  until todo.empty?
   n=todo.pop
   if boundary.call(n);stop.add(n);next;end
   next unless seen.add?(n)
   todo.concat(nodes[n]['dependencies'].select{|d|nodes[d]})
  end
  local[role]=seen;external[role]=stop
 end
 used=local.values.reduce(:|); ends=external.values.reduce(:|)
 fs=used.group_by{|n|source.call(n)}
 vertices=fs.sort.map do |p,ns|
  {'id'=>p,'kind'=>'file','label'=>File.basename(p,'.lean'),'folder'=>File.dirname(p).delete_prefix('Atlas/'),
   'file'=>p,'source_theorems'=>cache[p]['total'],'sha256'=>cache[p]['sha256'],
   'used_theorems'=>ns.count{|n|nodes[n]['kind']=='theorem'},
   'declarations'=>ns.sort.map{|n|{'name'=>n,'kind'=>nodes[n]['kind'],'file'=>p,'order'=>local['order'].include?(n),'simplicity'=>local['simplicity'].include?(n)}},
   'order'=>ns.any?{|n|local['order'].include?(n)},'simplicity'=>ns.any?{|n|local['simplicity'].include?(n)}}
 end
 ends.group_by{|n|boundary.call(n)}.sort.each do |b,ns|
  vertices<<{'id'=>'boundary:'+b,'kind'=>'boundary','label'=>b,'folder'=>'Reused prerequisites · proofs not expanded',
   'explore_group'=>(GROUPS.include?(b) ? b : {'Co0 / Leech isometries'=>'Co1','Shared Leech lattice'=>'Co1','Shared Fischer tensor / ray construction'=>'Fi24Prime'}[b]),
   'order'=>ns.any?{|n|external['order'].include?(n)},'simplicity'=>ns.any?{|n|external['simplicity'].include?(n)},
   'declarations'=>ns.sort.map{|n|{'name'=>n,'kind'=>nodes[n]['kind'],'file'=>source.call(n),'order'=>external['order'].include?(n),'simplicity'=>external['simplicity'].include?(n)}}}
 end
 roots[g].each{|role,n|vertices<<{'id'=>'root:'+role,'kind'=>'root','label'=>role=='order' ? "#{LABELS[g]} — exact order" : "#{LABELS[g]} — simplicity",'folder'=>n,'order'=>role=='order','simplicity'=>role=='simplicity','declarations'=>[{'name'=>n,'file'=>source.call(n),'kind'=>'theorem','order'=>role=='order','simplicity'=>role=='simplicity'}]}}
 edge_roles=Hash.new{|h,k|h[k]=Set.new}
 roots[g].each{|role,n|edge_roles[['root:'+role,source.call(n)]].add(role)}
 local.each do |role,ns|
  ns.each do |n|
   nodes[n]['dependencies'].each do |d|
    next unless nodes[d]
    a=source.call(n);b=boundary.call(d) ? 'boundary:'+boundary.call(d) : source.call(d)
    edge_roles[[a,b]].add(role) if a!=b
   end
  end
 end
 edges=edge_roles.sort.map{|(a,b),roles|{'from'=>a,'to'=>b,'order'=>roles.include?('order'),'simplicity'=>roles.include?('simplicity')}}
 # Validate acyclicity and transitive reduction, retaining role-specific reachability.
 index=vertices.to_h{|v|[v['id'],v]};raise 'Dangling edge' unless edges.all?{|e|index[e['from']]&&index[e['to']]}
 edges.each{|e|e['reduced_order']=false;e['reduced_simplicity']=false;e['reduced_all']=false}
 %w[all order simplicity].each do |role|
  es=edges.select{|e|role=='all'||e[role]};ch=es.group_by{|e|e['from']}.transform_values{|l|l.map{|e|e['to']}}
  reach={};active=Set.new;walk=nil
  walk=->(n){return reach[n] if reach[n];raise "Cycle #{g}: #{n}" unless active.add?(n);s=(ch[n]||[]).flat_map{|c|[c]+walk.call(c).to_a}.to_set;active.delete(n);reach[n]=s}
  index.each_key{|n|walk.call(n)}
  keep=es.reject{|e|(ch[e['from']]||[]).any?{|c|c!=e['to']&&reach[c].include?(e['to'])}}
  reduced_ch=keep.group_by{|e|e['from']}.transform_values{|l|l.map{|e|e['to']}}
  reduced_reach={};red=nil;red=->(n){reduced_reach[n]||=(reduced_ch[n]||[]).flat_map{|c|[c]+red.call(c).to_a}.to_set}
  index.each_key{|n|raise 'Reduction changed reachability' unless red.call(n)==reach[n]}
  keep.each{|e|e['reduced_'+role]=true}
 end
 data={'group'=>g,'display_label'=>LABELS[g],'groups'=>GROUPS.map{|key|{'key'=>key,'label'=>LABELS[key]}},'date'=>Time.now.utc.strftime('%Y-%m-%d'),'commit'=>commit,'audit'=>AUDIT,'audit_link'=>audit_link,'audit_date'=>audit_date,'release_header_binding'=>PUBLIC,'audited_commit'=>snapshot['commit'],
  'source_hashes_match'=>true,'full_closure_files'=>full[g].values.reduce(:|).map{|n|source.call(n)}.uniq.size,
  'nodes'=>vertices,'edges'=>edges,'roots'=>roots[g],
  'source_hashes'=>full[g].values.reduce(:|).map{|n|source.call(n)}.uniq.sort.to_h{|p|[p,cache[p]['sha256']]}}
 payload=JSON.generate(data).gsub('<','\\u003c')
 html=ERB.new(File.read(File.join(__dir__,'viewer.html.erb'))).result(binding)
 dest="verification/dependency-maps/#{g.downcase}";FileUtils.mkdir_p(dest);File.write(dest+"/#{g}.html",html)
 # Round-trip verifies self-contained data encoding.
 recovered=JSON.parse(html[/<script id="data" type="application\/json">(.*?)<\/script>/m,1])
 raise 'Embedded data mismatch' unless recovered==data
 summary={'group'=>g,'files'=>fs.size,'source_theorems'=>vertices.select{|v|v['kind']=='file'}.sum{|v|v['source_theorems']},'boundaries'=>ends.group_by{|n|boundary.call(n)}.keys.sort,'edges'=>edges.size}
 summaries<<summary;puts summary.to_json
end
readme=<<~MD
# Sporadic proof dependency diagrams

Each self-contained HTML file offers **Graph**, **Tree**, and **Files** views, with order/simplicity filters, a declaration inspector, theorem counts, search, and embedded downloadable data. No network or companion HTML files are needed to display it. Repository source and cross-group links require the adjacent checkout/pages.

| Group | Expanded source files | Named source theorems in those files | Collapsed prerequisites |
|---|---:|---:|---|
MD
summaries.each{|s|readme+="| [#{s['group']}](#{s['group'].downcase}/#{s['group']}.html) | #{s['files']} | #{s['source_theorems']} | #{s['boundaries'].join('; ')} |\n"}
readme+=<<~MD

Arrows point from a dependent file to a prerequisite. Cross-group nodes list the **exact declarations reused**, rather than implying reliance on another group's entire order-and-simplicity package. For example, M12 simplicity uses M11 simplicity; M11 uses M12 structure/order/action, not M12 simplicity. These are acyclic declaration dependencies even though informal group-level names can appear in both directions.

## Scope and counts

The data comes from the actual compiled type/value dependency graph in [the passed #{audit_date} audit](../../#{audit_link}), not imports. Every ATLAS source file in each complete closure is checked against the current evidence hashes. #{PUBLIC ? 'The historical dependency extraction predates the release licence-header update: exact comparison after that one header substitution verifies the correspondence; mathematical source is unchanged.' : 'Current hashes also match the dependency-audit snapshot exactly.'} Generation is a report, **not a new Lean proof recheck**. Lean/mathlib dependencies are omitted.

The public catalogue links open rendered diagrams on GitHub Pages. The HTML files can also be downloaded and opened locally; GitHub’s repository file viewer itself displays their source.

Named source theorem counts cover all named `theorem`/`lemma` commands in the file, including private ones, after removing comments and strings. “Used compiled” counts include generated proof helpers; definitions and instances are traversed but not counted as theorems. Whole-file totals may include unused or other-group statements in mixed files. Counts overlap between groups and are not additive. Boundary files/theorems are excluded from local totals; exact consumed declarations remain visible in the inspector.

Presentation boundaries are explicit in the generator. Named public sporadic modules, Mathieu/Co2/Co3/McL/HS modules, norm-six geometry, and Eisenstein/icosian models identify their respective constructions. Dodecad modules belong to M12. M24 expands its Golay/hexacode foundation; Co1 expands the Leech lattice and Co0 isometries; Fi24Prime expands the shared Fischer tensor/ray construction. Other pages collapse these packages and show their exact consumed declarations. Co0 is kept distinct from its simple quotient Co1; shared Fischer construction is not labeled as Fi24Prime simplicity. Fi22/Fi23 keep their common parameterized residue proofs visible. Generic lemmas and target-specific support stay expanded. These are presentation boundaries, not mathematical assumptions or a claim that every statement in a mixed source file concerns just one group.

The default graph removes transitive shortcut arrows while preserving reachability (checked separately for order, simplicity, and both). “All arrows” restores every recorded file edge. Shared tree branches link to their existing node.

## Regeneration

From the repository root:

```sh
ruby verification/dependency-maps/sporadic/generate.rb
```

The maintained inputs are `sporadic/generate.rb`, `sporadic/viewer.html.erb`, the repository sources, and the existing immutable audit. The fifteen HTML pages and this README are generated outputs. Redundant former standalone tree/graph files, intermediate JSON/CSV/DOT/Mermaid exports, and superseded M24-only generators have been removed. CSV/JSON can instead be downloaded from each page.
MD
File.write('verification/dependency-maps/README.md',readme)
