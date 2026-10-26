require 'json';require 'digest';require 'open3';require 'time'
b=__dir__
def command(*args)
 out,st=Open3.capture2e(*args);abort out unless st.success?;out
end
paths=['Atlas.lean']+Dir.glob('Atlas/**/*.lean')
tracked=command('git','ls-files').lines.map(&:strip)
info={time_utc:Time.now.utc.iso8601,path:Dir.pwd,branch:command('git','branch','--show-current').strip,commit:command('git','rev-parse','HEAD').strip,working_tree:command('git','status','--porcelain=v1','--untracked-files=all'),tracked_diff:command('git','diff','HEAD'),toolchain:File.read('lean-toolchain').strip,dependencies:JSON.parse(File.read('lake-manifest.json')),root_imports:File.readlines('Atlas.lean').grep(/^import /),sources:paths.to_h{|p|[p,{sha256:Digest::SHA256.file(p).hexdigest,lines:File.readlines(p).size,tracked:tracked.include?(p)}]},pins:%w[lean-toolchain lakefile.toml lake-manifest.json].to_h{|p|[p,Digest::SHA256.file(p).hexdigest]}}
info[:dependency_checkouts]=Dir.glob('.lake/packages/*/.git').to_h{|p|d=File.dirname(p);[d,command('git','-C',d,'rev-parse','HEAD').strip]}
File.write(b+'/SNAPSHOT.json',JSON.pretty_generate(info)+"\n")
File.write(b+'/SOURCE_SHA256SUMS',info[:sources].map{|p,v|"#{v[:sha256]}  #{p}\n"}.join)
puts "Snapshot #{info[:commit]}: #{paths.size} ATLAS source files"
