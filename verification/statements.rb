# Render recorded compiled signatures; never reconstruct theorem statements.
require 'json'
require 'zlib'
require 'digest'
Dir.chdir(File.expand_path('..',__dir__))
index=JSON.parse(File.read('verification/current.json'))
path=index.fetch('snapshot')+'/statements.log.gz'
raise 'Statement evidence hash mismatch' unless Digest::SHA256.file(path).hexdigest==index.fetch('evidence_files').fetch('statements.log.gz')
log=Zlib::GzipReader.open(path,&:read)
blocks={}
log.scan(/^STATEMENT (\S+) SOURCE (\S+)\n(.*?)(?=^STATEMENT |^SHARED EXTRACTION COMPLETE:|\z)/m){|name,mod,signature|blocks[name]=[mod,signature.rstrip]}
entries=JSON.parse(File.read('catalogue/catalogue.json')).fetch('entries')
text="# Principal compiled theorem statements\n\nGenerated from the successful compiled-declaration audit at source commit\n`#{index.fetch('source_commit')}`. These are verbatim elaborated `#check @name`\noutputs, with explicit parameters, typeclasses and universes; proof bodies are omitted.\nThe selections are the catalogue's primary order and simplicity interfaces.\nExact-exception and other structural results remain in the catalogue and full audit.\nDefinitions of the named models are linked through their source files; this is a\nsignature reference, not a self-contained definition of every dependency.\n\nThe source-bound [audit](AUDIT.md) records trust and verification scope.\nRegenerate using `ruby verification/statements.rb refresh`.\n\n"
entries.each do |entry|
 text+="## #{entry.fetch('label')}\n\n"
 model=entry.fetch('roles').fetch('model');text+="Model: `#{model.fetch('declaration')}` ([source](#{model.fetch('source')})).\n\n"
 %w[order simple].each do |role|
  ref=entry.fetch('roles').fetch(role);name=ref.fetch('declaration');mod,sig=blocks.fetch(name)
  raise "Missing signature #{name}" unless sig.start_with?('@'+name, name)
  text+="### #{role=='order' ? 'Order' : 'Simplicity'}\n\n`#{name}` — [source](#{ref.fetch('source')}).\n\n```lean\n#{sig}\n```\n\n"
 end
end
case ARGV.fetch(0,'check')
when 'refresh' then File.write('THEOREM_STATEMENTS.md',text)
when 'check' then raise 'Stale theorem statements' unless File.read('THEOREM_STATEMENTS.md')==text
else abort 'Usage: statements.rb [refresh|check]'
end
puts "PASS: #{entries.size*2} recorded compiled signatures."
