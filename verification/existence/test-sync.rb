# Lightweight publication-guard regression checks; no Lean processes or network.
require 'tmpdir'
require 'fileutils'
require 'open3'
require 'json'
require 'yaml'
root=File.expand_path('../..',__dir__)
def run_sync(dir,mode,expected,message=nil)
 out,err,status=Open3.capture3('ruby',dir+'/verification/existence/sync.rb',mode)
 raise "Unexpected #{mode} outcome: #{out}#{err}" unless status.success? == expected
 raise "Wrong refusal: #{err}" if message && !err.include?(message)
end
Dir.mktmpdir('atlas-contract-regression-') do |dir|
 FileUtils.mkdir_p(dir+'/verification')
 FileUtils.cp_r(root+'/verification/existence',dir+'/verification/existence')
 FileUtils.mkdir_p(dir+'/catalogue')
 FileUtils.cp(root+'/catalogue/catalogue.json',dir+'/catalogue/catalogue.json')
 FileUtils.cp(root+'/formalization.yaml',dir+'/formalization.yaml')
 %w[Atlas Atlas.lean lean-toolchain lakefile.toml lake-manifest.json].each{|p|FileUtils.ln_s(root+'/'+p,dir+'/'+p)}
 run_sync(dir,'check',true)
 p=dir+'/formalization.yaml'; original=File.read(p); doc=YAML.safe_load(original)
 doc['status']['main_results'].first['name']='stale name'; File.write(p,YAML.dump(doc))
 run_sync(dir,'check',false,'Stale formalization.yaml')
 run_sync(dir,'refresh',true)
 raise 'Refresh changed project-wide information' unless YAML.load_file(p)==YAML.safe_load(original)
 p=dir+'/verification/existence/Challenge.lean'; original=File.read(p)
 File.write(p,original.sub('theorem AtlasExistence.cyclic',"-- changed reference\ntheorem AtlasExistence.cyclic"))
 run_sync(dir,'refresh',false,'fresh Comparator check'); File.write(p,original)
 p=dir+'/verification/existence/Solution.lean'; original=File.read(p)
 File.write(p,original+"\naxiom forbidden : True\n")
 run_sync(dir,'check',false,'Unproved solution'); File.write(p,original)
 p=dir+'/catalogue/catalogue.json'; original=File.read(p); doc=JSON.parse(original)
 doc['entries']<<{'kind'=>'family','id'=>'family.NewUncovered'};File.write(p,JSON.generate(doc))
 run_sync(dir,'check',false,'Catalogue coverage changed');File.write(p,original)
 evidence=JSON.parse(File.read(dir+'/verification/existence/registry.json')).fetch('entries').first.fetch('evidence')
 p=dir+'/'+File.dirname(evidence)+'/SOURCE_HASHES.json'; original=File.read(p);doc=JSON.parse(original)
 doc['lean-toolchain']='0'*64;File.write(p,JSON.generate(doc))
 run_sync(dir,'check',false,'Stale evidence source');File.write(p,original)
 run_sync(dir,'check',true)
end
puts 'PASS: current evidence, stale YAML repair, changed contracts, forbidden solution placeholders, uncovered catalogue entries and stale source evidence.'
