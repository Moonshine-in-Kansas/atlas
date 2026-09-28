require_relative 'contracts'
require 'fileutils'
require 'time'
# Use the same renderer as the publication gate, without requiring existing evidence.
# Thus changed contracts can be prepared and checked before updating the evidence index.
def prepare_atlas_queue(scope, base)
  raise 'Supply a prepared parent harness' unless File.file?(base+'/lake-manifest.json')
  rows=AtlasContracts.entries.select{|r|r['scope']==scope}
  rendered=rows.to_h{|r|[r.fetch('declaration'),AtlasContracts.render(r)]}
  suffix=scope=='existence' ? 'split' : 'discriminators'
  out=AtlasContracts::ROOT+'/verification/results/existence-contract-'+suffix+'-'+Time.now.utc.strftime('%Y%m%dT%H%M%S%6NZ')
  raise 'Output already exists' if File.exist?(out)
  FileUtils.mkdir_p(out)
  queue=rows.map do |r|
    name=r.fetch('declaration'); dest=out+'/'+name.split('.').last
    FileUtils.mkdir_p(dest)
    rendered.fetch(name).each{|p,bytes|File.write(dest+'/'+p,bytes)}
    %w[lean-toolchain lakefile.toml lake-manifest.json].each{|p|FileUtils.cp(base+'/'+p,dest+'/'+p)}
    {target:name,harness:dest,status:'pending'}
  end
  File.write(out+'/QUEUE.json',JSON.pretty_generate(queue)+"\n")
  puts out
end
