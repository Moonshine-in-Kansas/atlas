require 'json'
require 'fileutils'
require 'time'
root=File.expand_path('../..',__dir__)
base=ARGV.fetch(0)
raise 'Supply previously prepared harness' unless File.file?(base+'/lake-manifest.json')
imports={
'cyclic'=>'Atlas.Families.Cyclic.Basic','alternating'=>'Atlas.Families.Alternating.Basic',
'typeA'=>'Atlas.LinearGroups.TypeA','typeB'=>'Atlas.LinearGroups.Orthogonal.BAllRanksConstruction',
'typeC'=>'Atlas.LinearGroups.TypeC','typeD'=>'Atlas.LinearGroups.Orthogonal.DConstruction',
'G2'=>'Atlas.LinearGroups.TypeG2','ReeG2'=>'Atlas.LinearGroups.TypeReeG2',
'M11'=>'Atlas.Sporadic.Mathieu11','M12'=>'Atlas.Sporadic.Mathieu12',
'M22'=>'Atlas.Sporadic.Mathieu22Simple','M23'=>'Atlas.Sporadic.Mathieu23',
'M24'=>'Atlas.Sporadic.Mathieu24Construction',
'Co1'=>'Atlas.Sporadic.Conway1','Co2'=>'Atlas.Sporadic.Conway2Construction',
'Co3'=>'Atlas.Sporadic.Conway3Construction','McL'=>'Atlas.Sporadic.McLaughlinConstruction',
'HS'=>'Atlas.Sporadic.HigmanSimsConstruction','Suz'=>'Atlas.Sporadic.SuzukiConstruction',
'J2'=>'Atlas.Sporadic.Janko2Construction','Fi22'=>'Atlas.Sporadic.Fischer22',
'Fi23'=>'Atlas.Sporadic.Fischer23','Fi24Prime'=>'Atlas.Sporadic.Fischer24Prime'}
config=JSON.parse(File.read(__dir__+'/comparator.json'))
parts=%w[Challenge Solution].to_h{|s|[s,File.read(__dir__+"/#{s}.lean").split(/(?=^theorem AtlasExistence\.)/)]}
out=root+'/verification/results/existence-contract-split-'+Time.now.utc.strftime('%Y%m%dT%H%M%SZ')
raise 'Output exists' if File.exist?(out)
FileUtils.mkdir_p(out)
queue=config.fetch('theorem_names').map do |name|
 label=name.split('.').last
 dest=out+'/'+label
 FileUtils.mkdir_p(dest)
 %w[Challenge Solution].each do |side|
   blocks=parts.fetch(side)
   selected=blocks.drop(1).select{|b|b.start_with?("theorem #{name} ")}
   raise "Missing/duplicate #{name}" unless selected.size==1
   header=blocks.first
   header=header.sub("import Atlas\n","import #{imports.fetch(label)}\n") if side=='Solution'
   File.write(dest+"/#{side}.lean",header+selected.first)
 end
 %w[lean-toolchain lakefile.toml lake-manifest.json].each{|p|FileUtils.cp(base+'/'+p,dest+'/'+p)}
 File.write(dest+'/comparator.json',JSON.pretty_generate(config.merge('theorem_names'=>[name]))+"\n")
 {target:name,harness:dest,status:'pending'}
end
File.write(out+'/QUEUE.json',JSON.pretty_generate(queue)+"\n")
puts out
