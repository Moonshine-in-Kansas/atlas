# Add/check one presentation-only column from maintained catalogue metadata.
require 'json'
require 'digest'
module AtlasDependencyLinks
  def self.run(mode)
    raise 'Expected refresh or check' unless %w[refresh check].include?(mode)
    data=JSON.parse(File.read('catalogue/catalogue.json'))
    text=File.read('CATALOGUE.md'); lines=text.lines
    header=lines.index{|l|l.start_with?('| Group or family |')}
    raise 'Missing release summary table' unless header
    old=lines[header].split('|').map(&:strip)[1...-1]
    old_index=old.index('Proof dependencies')||old.index('Lean files / theorems')
    wanted=old.reject{|v|['Proof dependencies','Lean files / theorems'].include?(v)}; insert=wanted.index('Order lines') or raise 'Missing line-count column'
    wanted.insert(insert,'Lean files / theorems')
    lines[header]='| '+wanted.join(' | ')+" |\n"
    separators=lines[header+1].split('|').map(&:strip)[1...-1]
    separators.delete_at(old_index) if old_index
    separators.insert(insert,'---');lines[header+1]='|'+separators.join('|')+"|\n"
    data.fetch('entries').each do |entry|
      anchor=entry.fetch('id').downcase.tr('.','-')
      idx=lines.index{|l|l.start_with?('| [')&&l.include?("](##{anchor})")};raise "Missing #{anchor}" unless idx
      path=entry['proof_dependencies'];link='—'
      if path
        raise 'Unsafe diagram path' unless path.match?(%r{\Averification/dependency-maps/[a-z][a-z0-9]*/[A-Z][A-Za-z0-9]*\.html\z})
        html=File.read(path);payload=html[/<script id="data" type="application\/json">(.*?)<\/script>/m,1] or raise "Missing data: #{path}"
        diagram=JSON.parse(payload)
        raise 'Wrong order root' unless diagram.dig('roots','order')==entry.dig('roles','order','declaration')
        raise 'Wrong simplicity root' unless diagram.dig('roots','simplicity')==entry.dig('roles','simple','declaration')
        diagram.fetch('source_hashes').each{|p,h|raise "Stale diagram source #{p}" unless Digest::SHA256.file(p).hexdigest==h}
        files=diagram.fetch('nodes').select{|n|n['kind']=='file'}
        count=files.sum{|n|n.fetch('source_theorems')}
        site=data['proof_dependencies_site']
        raise 'Unexpected diagram website' if site && site!='https://moonshine-in-kansas.github.io/atlas/'
        url=site ? site+path : path
        link="[#{files.size} / #{count}](#{url})"
      end
      cells=lines[idx].split('|').map(&:strip)[1...-1];cells.delete_at(old_index) if old_index;cells.insert(insert,link)
      lines[idx]='| '+cells.join(' | ')+" |\n"
    end
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
