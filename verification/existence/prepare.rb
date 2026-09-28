# Prepares the new existence contract; does not run a checker or change old evidence.
require_relative 'contracts'
require 'json'
require 'fileutils'
require 'digest'
require 'time'
root = File.expand_path('../..', __dir__)
config = AtlasContracts.config(AtlasContracts.entries.select { |r| r['scope']=='existence' }.map { |r| r.fetch('declaration') })
challenge = File.read(File.join(__dir__, 'Challenge.lean'))
solution = File.read(File.join(__dir__, 'Solution.lean'))
raise 'ATLAS import in reference' if challenge.lines.grep(/^import /).any? { |l| !l.start_with?('import Mathlib.') }
raise 'Reference imported by solution' if solution.match?(/^import .*Challenge/)
raise 'Unproved solution' if solution.match?(/\b(sorry|admit|axiom|native_decide)\b/)
expected = config.fetch('theorem_names').sort
[challenge, solution].each do |s|
  raise 'Target mismatch' unless s.scan(/^theorem (AtlasExistence\.\w+)/).flatten.sort == expected
end
raise 'Definition holes forbidden' unless config.fetch('definition_names').empty?
raise 'Unexpected axioms' unless config.fetch('permitted_axioms').sort == %w[propext Quot.sound Classical.choice].sort
if ARGV == ['--check']
  puts "PASS: #{expected.size} matched targets, mathlib-only reference imports, no solution placeholders."
  exit
end
raise 'Usage: prepare.rb [--check]' unless ARGV.empty?
out = File.join(root, 'verification/results/existence-contract-'+Time.now.utc.strftime('%Y%m%dT%H%M%SZ'))
raise 'Existing output directory' if File.exist?(out)
FileUtils.mkdir_p(out)
%w[Challenge.lean Solution.lean].each { |p| FileUtils.cp(File.join(__dir__, p), out) }
File.write(File.join(out, 'comparator.json'), JSON.pretty_generate(config)+"\n")
FileUtils.cp(File.join(root, 'lean-toolchain'), out)
File.write(File.join(out, 'lakefile.toml'), <<~TOML)
name = "AtlasExistenceContracts"
version = "0.1.0"
packagesDir = #{JSON.generate(File.join(root, '.lake/packages'))}
[leanOptions]
maxRecDepth = 10000
[[require]]
name = "Atlas"
path = #{JSON.generate(root)}
[[lean_lib]]
name = "Challenge"
[[lean_lib]]
name = "Solution"
TOML
hashes = %w[Challenge.lean Solution.lean comparator.json lean-toolchain lakefile.toml].to_h { |p| [p, Digest::SHA256.file(File.join(out,p)).hexdigest] }
File.write(File.join(out, 'PREPARATION.json'), JSON.pretty_generate({status:'prepared-not-checked',files:hashes})+"\n")
puts out
