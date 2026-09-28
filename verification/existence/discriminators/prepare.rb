require 'json'
require 'fileutils'
require 'time'
root=File.expand_path('../../..',__dir__)
config=JSON.parse(File.read(__dir__+'/comparator.json'))
parts=%w[Challenge Solution].to_h{|s|[s,File.read(__dir__+"/#{s}.lean").split(/(?=^theorem AtlasDistinguished\.)/)]}
names=config.fetch('theorem_names')
parts.each do |side,blocks|
 raise 'Mismatched targets' unless blocks.drop(1).map{|s|s[/^theorem (\S+)/,1]}.sort==names.sort
 raise 'Unproved solution' if side=='Solution' && blocks.join.match?(/\b(sorry|admit|axiom|native_decide)\b/)
end
raise 'Reference imports ATLAS' if parts['Challenge'].first.lines.grep(/^import /).any?{|l|!l.start_with?('import Mathlib.')}
raise 'Definition holes' unless config.fetch('definition_names').empty?
if ARGV==['--check']
 puts 'PASS: four same-witness invariant contracts; mathlib-only reference; no solution placeholders.'
 exit
end
base=ARGV.fetch(0)
raise 'Supply prepared parent harness' unless File.file?(base+'/lake-manifest.json')
imports={
 'typeB'=>%w[Atlas.LinearGroups.Orthogonal.BAllRanksConstruction Atlas.LinearGroups.Orthogonal.BInvolutionClasses],
 'typeC'=>%w[Atlas.LinearGroups.TypeC Atlas.LinearGroups.Symplectic.ProjectiveInvolutionCount],
 'alternating8'=>%w[Atlas.Families.Alternating.Basic Atlas.Comparisons.Exceptional.Order20160A8 Atlas.LinearGroups.UnitriangularFourProjective Atlas.GroupTheory.SylowCenterInvariant],
 'psl3Four'=>%w[Atlas.LinearGroups.TypeA Atlas.LinearGroups.UnitriangularThreeProjective Atlas.GroupTheory.SylowCenterInvariant]}
out=root+'/verification/results/existence-contract-discriminators-'+Time.now.utc.strftime('%Y%m%dT%H%M%SZ')
raise 'Output exists' if File.exist?(out)
FileUtils.mkdir_p(out)
queue=names.map do |name|
 label=name.split('.').last; dest=out+'/'+label;FileUtils.mkdir_p(dest)
 parts.each do |side,blocks|
  body=blocks.drop(1).find{|b|b.start_with?("theorem #{name} ")}
  header=blocks.first
  header=imports.fetch(label).map{|m|"import #{m}\n"}.join+header.lines.reject{|l|l.start_with?('import Atlas.')}.join if side=='Solution'
  File.write(dest+"/#{side}.lean",header+body)
 end
 %w[lean-toolchain lakefile.toml lake-manifest.json].each{|p|FileUtils.cp(base+'/'+p,dest+'/'+p)}
 File.write(dest+'/comparator.json',JSON.pretty_generate(config.merge('theorem_names'=>[name]))+"\n")
 {target:name,harness:dest,status:'pending'}
end
File.write(out+'/QUEUE.json',JSON.pretty_generate(queue)+"\n")
puts out
