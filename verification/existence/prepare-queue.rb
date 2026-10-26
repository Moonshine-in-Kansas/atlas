# Prepare current-export harnesses without building or running any checker.
# The three owner-deferred targets are always excluded.
require_relative 'contracts'
require 'fileutils'
out=ARGV.shift or abort 'Usage: ruby verification/existence/prepare-queue.rb NEW_DIRECTORY [TARGET...]'
out=File.expand_path(out)
abort 'Refusing to overwrite an existing directory' if File.exist?(out)
index=AtlasContracts::Index.new;result=index.validate!
names=ARGV.empty? ? result[:entries].select { |r|r['recorded_status']=='passed' }.map { |r|r['declaration'] } : ARGV
abort 'Unknown or duplicated target' unless names.uniq==names && (names-result[:entries].map { |r|r['declaration'] }).empty?
abort 'The three deferred targets remain open; no harness is prepared for them' unless (names & AtlasContracts::DEFERRED).empty?
FileUtils.mkdir_p(out)
result[:entries].select { |r|names.include?(r['declaration']) }.each do |r|
  dir=out+'/'+r.fetch('declaration');FileUtils.mkdir_p(dir)
  index.render(r).each { |p,s|File.binwrite(dir+'/'+p,s) }
  FileUtils.cp(index.root+'/lean-toolchain',dir+'/lean-toolchain')
  config=JSON.parse(File.read(dir+'/'+r['configuration']))
  File.write(dir+'/lakefile.toml',<<~TOML)
    name = "AtlasContractReplay"
    version = "1.2.0"
    packagesDir = #{JSON.generate(index.root+'/.lake/packages')}
    [[require]]
    name = "Atlas"
    path = #{JSON.generate(index.root)}
    [[lean_lib]]
    name = #{JSON.generate(config['challenge_module'])}
    [[lean_lib]]
    name = #{JSON.generate(config['solution_module'])}
  TOML
end
File.write(out+'/QUEUE.json',JSON.pretty_generate({status:'prepared-not-run',targets:names,deferred:AtlasContracts::DEFERRED,
  reference:'Exact reviewed inputs copied; only local package paths and package metadata adjusted',source_root:index.root})+"\n")
puts "Prepared #{names.size} harnesses in #{out}; three deferred targets untouched. No build or checker started."
