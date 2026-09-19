# Prepare an isolated harness using the recorded target selection; does not run a checker.
require 'json'
require 'fileutils'
require 'time'
root=File.expand_path('..',__dir__)
Dir.chdir(root)
abort 'Release metadata check failed' unless system('ruby','verification/release_metadata.rb','check')
index=JSON.parse(File.read('verification/current.json'))
snapshot=root+'/'+index.fetch('snapshot')
out=root+'/verification/results/comparator-'+Time.now.utc.strftime('%Y%m%dT%H%M%SZ')
raise 'Existing output' if File.exist?(out)
FileUtils.mkdir_p(out)
%w[Challenge.lean Solution.lean].each{|p|FileUtils.cp(snapshot+'/'+p,out+'/'+p)}
FileUtils.cp(snapshot+'/comparator-config.json',out+'/config.json')
FileUtils.cp('lean-toolchain',out+'/lean-toolchain')
# JSON quoted strings are valid TOML basic strings for these file paths.
File.write(out+'/lakefile.toml',<<~TOML)
name = "AtlasReleaseComparison"
version = "0.1.0"
packagesDir = #{JSON.generate(root+'/.lake/packages')}
[[require]]
name = "Atlas"
path = #{JSON.generate(root)}
[[lean_lib]]
name = "Challenge"
[[lean_lib]]
name = "Solution"
TOML
puts "Prepared #{out}\nRun lake update there, then the sandboxed comparator command in INDEPENDENT_CHECKERS.md."
