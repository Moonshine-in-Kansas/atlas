require 'zlib';require 'digest'
d=__dir__
large=Dir.children(d).select{|n|p=File.join(d,n);File.file?(p)&&File.size(p)>1_000_000&&!n.end_with?('.gz')}.sort
large.each do |n|
 Zlib::GzipWriter.open(File.join(d,n+'.gz')) do |g|
  g.mtime=0
  File.open(File.join(d,n),'rb'){|f|IO.copy_stream(f,g)}
 end
end
File.write(File.join(d,'.gitignore'),"# Large outputs remain readable locally; deterministic compressed copies are versioned.\n"+large.map{|n|"/#{n}\n"}.join)
File.write(File.join(d,'MANIFEST.sha256'),Dir.children(d).sort.reject{|n|n=='MANIFEST.sha256'}.filter_map{|n|p=File.join(d,n);next unless File.file?(p);"#{Digest::SHA256.file(p).hexdigest}  #{n}\n"}.join)
puts "Packaged #{large.size} large artifacts without deleting raw outputs."
