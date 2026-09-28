# Refresh derived metadata, or check it before publication. No Lean runs or uploads.
require_relative 'contracts'
require 'yaml'
require 'digest'
require 'zlib'
Dir.chdir(AtlasContracts::ROOT)
mode=ARGV.fetch(0,'check')
abort 'Usage: sync.rb [refresh|check]' unless %w[refresh check].include?(mode)
begin
  entries=AtlasContracts.entries
catalogue=JSON.parse(File.read('catalogue/catalogue.json')).fetch('entries').select{|e|%w[family sporadic].include?(e['kind'])}.map{|e|e.fetch('id')}.sort
covered=entries.select{|r|r['scope']=='existence'}.map{|r|r.fetch('catalogue_id')}.sort
raise 'Catalogue coverage changed: add reviewed existence contracts and registry entries before release' unless catalogue==covered
generated={}
  results=entries.map do |row|
    path=row.fetch('evidence')
    files=AtlasContracts.render(row)
    record=JSON.parse(File.read(path+'/RESULT.json'))
    raise "Fresh Comparator run required: #{row['declaration']}" unless record['status']=='passed' && record['exit_code']==0 && record['inputs_unchanged'] && !record['memory_guard_stop']
    files.each do |name,bytes|
      raise "Changed #{row['declaration']} #{name}: prepare and run a fresh Comparator check" unless File.binread(path+'/'+name)==bytes.b
      raise "Invalid input hash: #{path}/#{name}" unless Digest::SHA256.hexdigest(bytes)==record.fetch('files').fetch(name)
    end
    source_path=File.dirname(path)+'/SOURCE_HASHES.json'
    sources=JSON.parse(File.read(source_path))
    required=(Dir.glob('Atlas/**/*.lean')+%w[Atlas.lean lean-toolchain lakefile.toml lake-manifest.json]).sort
    raise "Incomplete source map: #{path}" unless sources.keys.sort==required
    sources.each{|p,h|raise "Stale evidence source #{p}; fresh Comparator check required" unless Digest::SHA256.file(p).hexdigest==h}
    Zlib::GzipReader.open(path+'/comparator.log.gz') do |z|
      digest=Digest::SHA256.new
      while (chunk=z.read(1024*1024)) && !chunk.empty?
        digest.update(chunk)
      end
      raise "Invalid Comparator log: #{path}" unless digest.hexdigest==record.fetch('log_sha256')
    end
    result={'name'=>row.fetch('name'),'declaration'=>row.fetch('declaration'),
      'file'=>path+'/Solution.lean','comparator_config'=>path+'/comparator.json',
      'result_record'=>path+'/RESULT.json','sorry_count'=>0}
    result['additional_statement']=row['additional_statement'] if row.key?('additional_statement')
    result
  end
  AtlasContracts::SCOPES.each do |scope,(path,_)|
    rows=entries.select{|r|r['scope']==scope}
    generated[path+'/comparator.json']=JSON.pretty_generate(AtlasContracts.config(rows.map{|r|r['declaration']}))+"\n"
  end
  generated['verification/existence/targets.json']=JSON.pretty_generate(entries.select{|r|r['scope']=='existence'}.map{|r|{'declaration'=>r['declaration'],'scope'=>'existence, exact order, simplicity and commutativity/noncommutativity on one witness'}})+"\n"
  doc=YAML.load_file('formalization.yaml')
  expected=Marshal.load(Marshal.dump(doc))
  expected.fetch('status')['main_results']=results
  expected.fetch('verification')['reports']=[['existence','existence'],['strengthened-existence','discriminators']].map do |kind,scope|
    n=entries.count{|r|r['scope']==scope}
    {'kind'=>kind,'file'=>AtlasContracts::SCOPES.fetch(scope).first+'/RESULTS.md','passed'=>n,'total'=>n}
  end
  if mode=='refresh'
    # Preserve all project-wide prose, comments and formatting unless derived values changed.
    File.write('formalization.yaml',YAML.dump(expected)) unless doc==expected
    generated.each{|p,bytes|File.write(p,bytes) unless File.file?(p)&&File.binread(p)==bytes.b}
  else
    raise 'Stale formalization.yaml: run sync.rb refresh' unless doc==expected
    generated.each{|p,bytes|raise "Stale #{p}: run sync.rb refresh" unless File.binread(p)==bytes.b}
  end
  puts "PASS: #{results.size} indexed contracts match reviewed statements, immutable successful evidence and current sources (#{mode})."
rescue StandardError => e
  warn "Contract metadata refused: #{e.message}"
  exit 1
end
