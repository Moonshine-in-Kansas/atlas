require 'json'
source, out = ARGV
raise 'Expected source attempt and new evidence directory' unless source && out
inventory=File.readlines(source+'/inventory.jsonl').map { |l| JSON.parse(l) }
roots=inventory.to_h { |r| [r.fetch('declaration'),r] }
names=['']
excluded=[]
output=STDOUT
output.binmode
File.foreach(source+'/proofs.ndjson') do |line|
  if line.start_with?('{"in":')
    r=JSON.parse(line)
    c=r['str'] || r.fetch('num')
    p=names.fetch(c.fetch('pre'))
    s=c['str'] || c.fetch('i').to_s
    names[r['in']]=p.empty? ? s : p+'.'+s
  elsif line.start_with?('{"def":') && line.include?('"safety":"partial"')
    r=JSON.parse(line).fetch('def')
    name=names.fetch(r.fetch('name'))
    raise 'Unexpected partial declaration outside root inventory' unless roots.key?(name)
    raise 'Unexpected partial declaration kind' unless name.end_with?('._unsafe_rec') && !roots[name]['theorem']
    excluded << {declaration:name,inventory:roots[name],export_record:r,original_line:line}
    next
  end
  output.write(line)
end
output.flush
raise 'Expected exactly 45 generated partial implementations' unless excluded.size==45
File.write(out+'/EXCLUDED_IMPLEMENTATIONS.json',JSON.pretty_generate(excluded)+"\n")
excluded_names=excluded.map { |r| r[:declaration] }
File.open(out+'/inventory.jsonl','w') do |f|
  inventory.each { |r| f.puts(JSON.generate(r)) unless excluded_names.include?(r['declaration']) }
end
warn "Removed exactly #{excluded.size} compiler implementation records; all other export bytes retained"
