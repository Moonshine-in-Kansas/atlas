#!/usr/bin/env ruby
# Run ONLY after all six full audits have passed and artifact review is complete.
# Usage, from /home/gerald/atlas:
#   ruby /tmp/record-unitary-final.rb /absolute/path/to/unitary-final-runs.json
# Input is an explicit {scope: "verification/runs/checkpoint/run"} map.
# This script does NOT run Lean, refresh generated catalogue files, commit or publish.
require 'json'
require 'digest'
require 'fileutils'
require 'pathname'
require 'zlib'

ROOT = '/home/gerald/atlas'
SCOPES = {
  'order' => 'unitary-projective-order',
  'generation' => 'unitary-generation-complete',
  'simplicity' => 'unitary-simplicity-complete',
  'exceptions' => 'unitary-exceptions-complete',
  'transport' => 'unitary-transport-complete',
  'structure' => 'unitary-public'
}.freeze
BASE = 'verification/unitary/construction'
EVIDENCE_ID = 'unitary-family-v1'

abort 'Supply exactly one explicit six-scope run-path JSON file' unless ARGV.size == 1
input = File.expand_path(ARGV.fetch(0))
Dir.chdir(ROOT)
require File.join(ROOT, 'docs/catalogue/manage')
paths = JSON.parse(File.read(input))
abort 'Expected exactly six independent unitary scopes' unless paths.keys.sort == SCOPES.keys.sort
read = lambda do |path|
  File.file?(path) ? File.binread(path) : Zlib::GzipReader.open(path + '.gz', &:read).b
end
load_json = ->(path) { JSON.parse(read.call(path)) }
sha = ->(path) { Digest::SHA256.hexdigest(read.call(path)) }
write_json = ->(value) { JSON.pretty_generate(value) + "\n" }

# Reject misleading paths and unsuccessful or wrong-scope records before any output.
paths.each do |scope, path|
  abort "Invalid run path for #{scope}" unless path.is_a?(String) &&
    path.start_with?('verification/runs/') && Pathname.new(path).cleanpath.to_s == path
  result = load_json.call(path + '/RESULT.json')
  checkpoint = load_json.call(path + '/CHECKPOINT.json')
  abort "Unaccepted full audit: #{scope}" unless result['status'] == 'passed' &&
    result['mode'] == 'full' && result['checkpoint'] == SCOPES.fetch(scope) &&
    checkpoint['id'] == SCOPES.fetch(scope) && checkpoint['mode'] == 'full' &&
    checkpoint['definitions'] == true
end
main = paths.fetch('structure')
snapshot = load_json.call(main + '/SNAPSHOT.json')
nodes = read.call(main + '/dependencies.jsonl').lines.map { |line| JSON.parse(line) }
  .to_h { |node| [node.fetch('name'), node] }
roots = read.call(main + '/declarations.jsonl').lines.map { |line| JSON.parse(line).fetch('declaration') }
ref = lambda do |name, theorem: true|
  abort "Not a selected public audit root: #{name}" unless roots.include?(name)
  node = nodes.fetch(name)
  abort "Not a compiled theorem: #{name}" if theorem && node.fetch('kind') != 'theorem'
  { 'declaration' => name, 'source' => node.fetch('module').tr('.', '/') + '.lean' }
end

parameters = 'F finite with q=|F|, K/F an actual quadratic extension; n is matrix dimension; ' \
  'stable catalogue: n>=3 and (n,q)!=(3,2)'
exceptions = 'The full theorem covers n>=2 and has exactly (2,2), (2,3), (3,2) as nonsimple cases. ' \
  'Dimension two is retained through the actual PSU2(F)≃PSL2(F) comparison.'
formula = 'q^(n*(n-1)/2) * product_{i=2..n}(q^i-(-1)^i) / gcd(n,q+1)'
roles = {
  'model' => ref.call('Atlas.Unitary.PSU', theorem: false),
  'finite' => ref.call('Atlas.Unitary.finite_psu'),
  'order' => ref.call('Atlas.Unitary.card_psu_factor').merge('formula' => formula),
  'simple' => ref.call('Atlas.Unitary.simple_of_good'),
  'nonabelian' => ref.call('Atlas.Unitary.noncommutative_of_good')
}
descriptions = {
  'Atlas.Unitary.transvectionGenerated_two_eq_top' => 'Actual SU2 transvection generation over every finite base field, including q=2 and q=3',
  'Atlas.Unitary.transvectionGenerated_eq_top_of_not_three_binary' => 'Actual SU generation for all dimensions n>=2 except precisely the binary dimension-three case',
  'Atlas.type2A_construction' => 'Construction record for the actual special-unitary matrix group and its center quotient',
  'Atlas.type2A_prime_power' => 'Actual quadratic finite-field and matrix-quotient witnesses for p prime, f>=1 and every positive simplicity parameter',
  'Atlas.exists_type2A' => 'Existence with an explicit equivalence to the retained projective special-unitary carrier',
  'Atlas.Unitary.simple_iff_good' => 'Exact simplicity criterion in every matrix dimension n>=2, excluding precisely (2,2), (2,3), (3,2)',
  'Atlas.Unitary.card_psu_mul_gcd' => 'Division-free projective order identity with the full scalar-center factor',
  'Atlas.Unitary.transvectionGenerated_eq_top_of_good' => 'Actual line transvections generate SU in every positive simplicity case, including the binary rank-four base',
  'Atlas.Unitary.special_perfect_of_good' => 'Perfectness of the actual special-unitary carrier throughout the positive simplicity range',
  'Atlas.Unitary.isotropic_primitive' => 'Primitivity of the actual projective action on isotropic K-lines for n>=2',
  'Atlas.Unitary.projectiveEmbedding_injective' => 'Faithful map from the actual center quotient into PGL over the quadratic extension',
  'Atlas.Unitary.card_isotropicPoints' => 'Uniform isotropic K-line count, with denominator q^2-1',
  'Atlas.Unitary.center_eq_scalarSubgroup' => 'Full SU center equals the actual norm-one scalar subgroup satisfying lambda^n=1',
  'Atlas.Unitary.card_center' => 'Exact full scalar-center order gcd(n,q+1)',
  'Atlas.Unitary.graphFieldAutomorphism_involutive' => 'The actual inverse-conjugate-transpose graph-field automorphism of SL is involutive; no projective fixed-point claim',
  'Atlas.Unitary.card_threeRootGroup' => 'The actual full three-dimensional unipotent subgroup has order q^3 in every characteristic',
  'Atlas.Unitary.threeRootGroup_center_iff' => 'Exact center of that unipotent subgroup: first parameter zero and trace-zero second parameter',
  'Atlas.Unitary.OrderChecks.psu_three_ternary_simple' => 'Positive simplicity regression for the actual PSU3(3)',
  'Atlas.Unitary.OrderChecks.psu_four_binary_simple' => 'Positive simplicity regression for the actual PSU4(2)',
  'Atlas.Unitary.OrderChecks.psu_four_ternary_simple' => 'Positive simplicity regression for the actual PSU4(3)',
  'Atlas.Unitary.OrderChecks.psu_five_binary_simple' => 'Positive simplicity regression for PSU5(2), exercising the binary higher-dimensional induction',
  'Atlas.Unitary.OrderChecks.psu_two_binary_not_simple' => 'Actual nonsimplicity regression for PSU2(2)',
  'Atlas.Unitary.OrderChecks.psu_two_ternary_not_simple' => 'Actual nonsimplicity regression for PSU2(3)',
  'Atlas.Unitary.OrderChecks.psu_three_binary_not_simple' => 'Actual nonsimplicity regression for PSU3(2), through its proved proper nontrivial normal subgroup',
  'Atlas.Unitary.OrderChecks.points_three_ternary' => 'The PSU3(3) isotropic action has 28 points',
  'Atlas.Unitary.OrderChecks.points_four_binary' => 'The PSU4(2) isotropic action has 45 points',
  'Atlas.Unitary.OrderChecks.psu_two_quaternary_regression' => 'An actual quadratic-field PSU2(4) witness has order 60 and is nonabelian simple'
}.freeze
properties = descriptions.map { |name, description| ref.call(name).merge('description' => description) }

registry_path = 'docs/catalogue/catalogue.json'
registry_original = File.binread(registry_path)
registry = JSON.parse(registry_original)
old_entry = registry.fetch('entries').select { |e| e['id'] == 'family.PSU' }
abort 'Expected exactly one existing family.PSU entry' unless old_entry.size == 1
abort 'Unexpected existing unitary evidence policy' unless old_entry.first['evidence'].nil? ||
  old_entry.first['evidence'] == EVIDENCE_ID
entry = old_entry.first.merge(
  'label' => 'PSU / twisted A', 'kind' => 'family', 'audit_entry' => 'PSU',
  'proof_status' => 'construction_complete',
  'construction' => 'Actual standard Hermitian SU_n(K/F), quotiented by its proved full norm-one scalar center',
  'parameters' => parameters, 'exceptions' => exceptions,
  'recognition' => 'Direct finite Hermitian matrix construction, with actual field transport and SL graph-field fixed-subgroup identification; no order recognition, CFSG or projective fixed-point assertion',
  'attribution' => 'ATLAS quadratic-extension, Hermitian norm-count, Witt-coordinate, transvection and Iwasawa proofs; pinned mathlib field and matrix infrastructure',
  'roles' => roles, 'properties' => properties, 'evidence' => EVIDENCE_ID,
  'presentation' => {
    'label' => '²Aₙ(q)',
    'construction' => 'PSU_(n+1)(K/F), the actual Hermitian scalar quotient',
    'parameters' => 'Lie rank n>=2; simple except (n,q)=(2,2)',
    'order' => 'q^(n*(n+1)/2) * product_{i=2..n+1}(q^i-(-1)^i) / gcd(n+1,q+1)',
    'note' => 'The catalogue table uses Lie rank n. Lean declarations use matrix dimension d=n+1 and q=|F|, not |K|=q^2. The complete dimension-d theorem begins at d=2 and has exactly three exceptions. The stable catalogue starts at d=3; dimension two has the actual PSL comparison. Field and fixed-subgroup equivalences are included verbatim in the public theorem extract.'
  }
)
row = {
  'entry' => 'PSU', 'kind' => 'family',
  'checking' => 'checked: independent full structure, order, generation, simplicity, exceptions and transport audits',
  'parameters' => parameters, 'order' => formula,
  'model' => roles['model']['declaration'], 'finiteness_theorem' => roles['finite']['declaration'],
  'order_theorem' => roles['order']['declaration'], 'simplicity_theorem' => roles['simple']['declaration'],
  'noncommutativity' => roles['nonabelian']['declaration']
}
inventory = {
  'groups' => [row], 'properties' => properties.map { |p| p.merge('entry' => 'Atlas.Unitary') },
  'catalogue_scope' => entry.slice('id', 'label', 'kind', 'audit_entry', 'proof_status',
    'construction', 'parameters', 'exceptions')
}
runs = paths.transform_values { |path| { 'directory' => path, 'manifest_sha256' => sha.call(path + '/SHA256SUMS') } }
statements = read.call(main + '/statements.log')
artifacts = {
  'ENTRY.json' => write_json.call(entry), 'INVENTORY.json' => write_json.call(inventory),
  'RUNS.json' => write_json.call(runs), 'RUN_PATHS.json' => write_json.call(paths),
  'THEOREM_STATEMENTS.txt' => statements, 'record-unitary-final.rb' => File.binread(__FILE__)
}
# Existing completed evidence is immutable. Different runs require a deliberate parent-side migration.
artifacts.each do |name, content|
  path = BASE + '/' + name
  abort "Refusing to overwrite different evidence: #{path}" if File.exist?(path) && File.binread(path) != content
end
FileUtils.mkdir_p(BASE)
artifacts.each { |name, content| File.binwrite(BASE + '/' + name, content) }
manifest = artifacts.keys.sort.map { |name| "#{Digest::SHA256.file(BASE + '/' + name).hexdigest}  #{name}\n" }.join
File.binwrite(BASE + '/MANIFEST.sha256', manifest)
evidence = {
  'format' => EVIDENCE_ID, 'directory' => BASE, 'manifest' => BASE + '/MANIFEST.sha256',
  'manifest_sha256' => Digest::SHA256.hexdigest(manifest),
  'source_commit' => snapshot.fetch('commit'), 'toolchain' => snapshot.fetch('toolchain'),
  'statements' => BASE + '/THEOREM_STATEMENTS.txt'
}
File.binwrite(BASE + '/EVIDENCE.json', write_json.call(evidence))

# The established loader checks bound artifacts, full dependency policy, all actual source
# dependency hashes, pins, toolchains, selected roots and the independent order boundary.
AtlasCatalogue.unitary_family_evidence(evidence, check_sources: true)
registry.fetch('evidence')[EVIDENCE_ID] = evidence
# Move only the formerly planned PSU record next to PSL; preserve every other record and
# their relative order, so completed families remain before the sporadic groups.
registry['entries'] = registry.fetch('entries').reject { |e| e['id'] == 'family.PSU' }
psl_index = registry['entries'].index { |e| e['id'] == 'family.PSL' }
abort 'Missing existing PSL family anchor' unless psl_index
registry['entries'].insert(psl_index + 1, entry)
AtlasCatalogue.validate(registry, check_sources: true)
abort 'Registry changed during preparation; refusing to overwrite owner work' unless File.binread(registry_path) == registry_original
File.binwrite(registry_path, write_json.call(registry))
puts "Recorded one actual PSU family and #{properties.size} selected theorem properties."
puts 'Next, parent runs the standard catalogue refresh/check and records their fresh evidence.'
