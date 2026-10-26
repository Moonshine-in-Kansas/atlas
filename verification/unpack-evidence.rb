# Verify losslessly compressed evidence against its original recorded bytes.
require 'json'
require 'digest'
require 'zlib'
root=File.expand_path('..',__dir__)
abort 'Usage: ruby verification/unpack-evidence.rb --check' unless ARGV==['--check']
index=JSON.parse(File.read(root+'/verification/compressed-evidence.json'))
index.each do |original,r|
  path=root+'/'+r.fetch('path')
  raise "Compressed hash mismatch: #{path}" unless Digest::SHA256.file(path).hexdigest==r.fetch('sha256')
  digest=Digest::SHA256.new;size=0
  Zlib::GzipReader.open(path) do |g|
    until g.eof?
      chunk=g.read(1024*1024);digest.update(chunk);size+=chunk.bytesize
    end
  end
  raise "Original hash mismatch: #{original}" unless digest.hexdigest==r.fetch('uncompressed_sha256') && size==r.fetch('uncompressed_bytes')
end
puts "PASS: #{index.size} compressed evidence artifacts match their original bytes."
