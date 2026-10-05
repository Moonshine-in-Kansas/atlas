# Add/check one presentation-only column from maintained catalogue metadata.
require 'json'
require 'digest'
require 'csv'
require 'zlib'
require 'set'
module AtlasDependencyLinks
  def self.run(mode)
    raise 'Expected refresh or check' unless %w[refresh check].include?(mode)
    data=JSON.parse(File.read('catalogue/catalogue.json'))
    text=File.read('CATALOGUE.md'); lines=text.lines
    header=lines.index{|l|l.start_with?('| Group or family |')}
    raise 'Missing release summary table' unless header
    old=lines[header].split('|').map(&:strip)[1...-1]
    old_index=old.index('Proof dependencies')||old.index('Lean files / theorems')
wanted=['Group or family','Order','Proven simplicity','Lean files / theorems','Intrinsic lines','Total dependency lines']
lines[header]='| '+wanted.join(' | ')+" |\n"
lines[header+1]="|---|---|---|---|---:|---:|\n"
ranges=JSON.parse(Zlib::GzipReader.open('catalogue/line-ranges.json.gz', &:read))
measured=CSV.read('catalogue/proof-line-counts.csv',headers:true)
family_owner=->(p) do
  case p
  when %r{Atlas/LinearGroups/ReeG2/}, %r{Atlas/LinearGroups/TypeReeG2} then 'family.ReeG2'
  when %r{Atlas/LinearGroups/G2/}, %r{Atlas/LinearGroups/TypeG2} then 'family.G2'
  when %r{Atlas/LinearGroups/Symplectic/}, %r{Atlas/LinearGroups/TypeC} then 'family.C'
  when %r{Atlas/LinearGroups/Orthogonal/B(?:[12]|Family|AllRanks)[^/]*\.lean$} then 'family.B'
  when %r{Atlas/LinearGroups/Orthogonal/D[^/]*\.lean$} then nil # Includes shared determinant infrastructure.
  when %r{Atlas/LinearGroups/(PSL|ProjectiveSpecialLinear|ProjectiveGeneralLinear|Elementary\.lean)} then 'family.PSL'
  else nil
  end
end
    data.fetch('entries').each do |entry|
      anchor=entry.fetch('id').downcase.tr('.','-')
      idx=lines.index{|l|l.start_with?('| [')&&l.include?("](##{anchor})")};raise "Missing #{anchor}" unless idx
      path=entry['proof_dependencies'];link='—';files=nil
      if path
        raise 'Unsafe diagram path' unless path.match?(%r{\Averification/dependency-maps/[a-z][a-z0-9]*/[A-Z][A-Za-z0-9]*\.html\z})
        html=File.read(path);payload=html[/<script id="data" type="application\/json">(.*?)<\/script>/m,1] or raise "Missing data: #{path}"
        diagram=JSON.parse(payload)
        raise 'Wrong order root' unless diagram.dig('roots','order')==entry.dig('roles','order','declaration')
        raise 'Wrong simplicity root' unless ([entry.dig('roles','simple','declaration')]+entry.fetch('properties',[]).map{|p|p['declaration']}).include?(diagram.dig('roots','simplicity'))
        diagram.fetch('source_hashes').each{|p,h|raise "Stale diagram source #{p}" unless Digest::SHA256.file(p).hexdigest==h}
        files=diagram.fetch('nodes').select{|n|n['kind']=='file'}
        count=files.sum{|n|n.fetch('source_theorems')}
        site=data['proof_dependencies_site']
        raise 'Unexpected diagram website' if site && site!='https://moonshine-in-kansas.github.io/atlas/'
        url=site ? site+path : path
        link="[#{files.size} / #{count}](#{url})"
      end
  allowed=[entry.dig('roles','simple','declaration')]+entry.fetch('properties',[]).map{|p|p['declaration']}
  row=measured.find{|r|r['order_root']==entry.dig('roles','order','declaration')&&allowed.include?(r['simplicity_root'])} or raise 'Missing measured roots'
  union=Hash.new{|h,k|h[k]=Set.new}
  %w[order_root simplicity_root].each{|k|ranges.fetch(row[k]).each{|p,rs|rs.each{|lo,hi|union[p].merge(lo..hi)}}}
  total=union.values.sum(&:size)
  raise 'Range/total mismatch' unless total==row['atlas_union_lines'].to_i
  expanded=files&.map{|f|f['file']}&.to_set
  intrinsic=union.sum{|p,ls| (expanded ? expanded.include?(p) : (family_owner.call(p).nil? || family_owner.call(p)==entry['id'])) ? ls.size : 0}
  format_count=->(n){n.to_s.reverse.scan(/.{1,3}/).join(',').reverse}
  cells=lines[idx].split('|').map(&:strip)[1...-1].first(3)
  lines[idx]='| '+(cells+[link,format_count.call(intrinsic),format_count.call(total)]).join(' | ')+" |\n"
end
note=lines.index{|l|l.start_with?('**Line-count convention')}
raise 'Missing count convention' unless note
lines[note]="**Line-count convention:** both columns combine order and simplicity, counting each required ATLAS declaration source line once. **Intrinsic lines** restrict this union to the diagram’s expanded files: collapsed groups and shared construction packages are excluded. Families exclude identifiable reused family modules; generic supporting lemmas remain included. This is a documented source-module convention, not a claim that every line is unique to one group. **Total dependency lines** include all transitive ATLAS prerequisites, including reused groups and shared constructions. Both exclude Lean/mathlib and include comments/blank lines within declaration ranges; neither counts whole files. File/theorem counts describe expanded files, whereas line counts include only required declaration ranges. Rows overlap and must not be added. The [original measurements](catalogue/proof-line-counts.csv) and [source ranges](catalogue/line-ranges.json.gz) retain the separate audit data from 17 September 2026; the mathematical sources are unchanged.\n"
    generated=lines.join
    if mode=='refresh';File.write('CATALOGUE.md',generated)
    else;raise 'Stale proof-dependency catalogue column' unless text==generated;end
    puts "PASS: catalogue proof-dependency column and source bindings (#{mode})."
  end
end
if $PROGRAM_NAME==__FILE__
  Dir.chdir(File.expand_path('../..',__dir__))
  AtlasDependencyLinks.run(ARGV.fetch(0,'check'))
end
