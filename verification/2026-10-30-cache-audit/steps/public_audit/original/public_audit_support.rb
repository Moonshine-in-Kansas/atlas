# SOURCE-ONLY PROPOSAL. Not installed, syntax-checked, or executed.
# Registration and metadata only: the parent owns every computational guard,
# extraction, policy evaluation, compression and successful RESULT commit.
require 'json'
require 'digest'
require 'fileutils'

module AtlasPublicAuditRegistration
  PROTOCOL = 'atlas-registered-whole-public-audit-v1'.freeze
  AXIOMS = %w[propext Classical.choice Quot.sound].freeze
  PINS = %w[lean-toolchain lakefile.toml lake-manifest.json].freeze
  CATALOGUES = %w[catalogue/catalogue.json catalogue/realizations.json
    catalogue/comparisons.json catalogue/checkpoints.json].freeze
  COLLECTOR_CODE = %w[verification/release_metadata.rb verification/release_evidence.rb
    verification/existence/contracts.rb verification/parent_receipts.rb verification/policy.rb].freeze
  BASELINE = 'claude/release-v1.2-20261026/candidate'.freeze
  BASELINE_ROOTS_SHA256 = '063e4d2f12380a07737a301b7a95336a52e2042f018c7ab58c4854d860df289e'.freeze
  BASELINE_ROOT_COUNT = 1207
  MANIFEST_PATH = 'public-manifests/whole-public-roots.json'.freeze

  def self.sha(path) = Digest::SHA256.file(path).hexdigest
  def self.json_bytes(value) = JSON.pretty_generate(value) + "\n"

  def self.relative!(path)
    raise 'Unsafe relative public input' unless path.is_a?(String) && !path.empty? &&
      !path.start_with?('/') && !path.include?("\0") &&
      path.split('/').none? { |part| part.empty? || %w[. ..].include?(part) }
    path
  end

  def self.input(base, relative)
    cursor = File.expand_path(base)
    raise 'Symlinked public input base' if File.symlink?(cursor)
    relative!(relative).split('/').each do |part|
      cursor = File.join(cursor, part)
      raise 'Symlinked public input' if File.symlink?(cursor)
    end
    raise "Missing public input #{cursor}" unless File.file?(cursor)
    cursor
  end

  def self.unchanged!(bindings)
    bindings.each do |path, digest|
      raise "Public registration input changed: #{path}" unless sha(path) == digest
    end
  end

  def self.write_new(directory, relative, bytes)
    path = File.join(directory, relative!(relative))
    raise 'Preserve prior public artifact' if File.exist?(path) || File.symlink?(path)
    cursor = File.expand_path(directory)
    relative.split('/')[0...-1].each do |part|
      cursor = File.join(cursor, part)
      raise 'Symlinked public output directory' if File.symlink?(cursor)
    end
    FileUtils.mkdir_p(File.dirname(path))
    File.open(path, File::WRONLY | File::CREAT | File::EXCL, 0o644) do |io|
      io.binmode; io.write(bytes); io.flush; io.fsync
    end
    path
  end

  # Call the installed gate's real collector. Do not copy its recursive selector,
  # substitute the addition scopes, or run Gate#run/full publication acceptance.
  def self.snapshot(task:, root:)
    task = File.expand_path(task); root = File.expand_path(root)
    candidate = task + '/candidate'
    code = COLLECTOR_CODE.to_h { |p| [p, sha(input(candidate, p))] }
    require input(candidate, 'verification/release_metadata.rb')
    method_file = AtlasReleaseMetadata::Gate.instance_method(:validate_sources!).source_location.first
    raise 'Public selector is not the candidate gate' unless File.realpath(method_file) ==
      File.realpath(input(candidate, 'verification/release_metadata.rb'))
    raise 'Completed-checkpoint selector is not installed' unless defined?(AtlasReleaseEvidence) &&
      File.realpath(AtlasReleaseEvidence.method(:checkpoints).source_location.first) ==
      File.realpath(input(candidate, 'verification/release_evidence.rb'))
    loaded = $LOADED_FEATURES.map { |p| File.expand_path(p) }.select { |p| p.start_with?(candidate + '/') }
    raise 'Unregistered collector code dependency' unless
      (loaded - COLLECTOR_CODE.map { |p| candidate + '/' + p }).empty?
    reader_class = Class.new(AtlasContracts::Index) do
      attr_reader :observed
      def initialize(root)
        @observed = {}
        super(root)
      end
      def read(path)
        data = super(path)
        digest = Digest::SHA256.hexdigest(data)
        raise 'Metadata changed while selecting public roots' if @observed.key?(path) && @observed[path] != digest
        @observed[path] = digest
        data
      end
    end
    reader = reader_class.new(candidate)
    gate = AtlasReleaseMetadata::Gate.new(candidate, reader: reader)
    raise 'Finalize the actual checkpoint catalogue before registration' unless
      gate.index['completed_checkpoints'] == 'catalogue/checkpoints.json' && gate.index['source_update']
    gate.validate_sources!
    roots = gate.roots
    raise 'Public target layout differs from the gate collector' unless roots.all? { |t|
      t.keys.sort == %w[declaration kind module] && t.fetch('kind') == 'any' }
    # In particular, Mathlib defining modules are valid here.
    roots_path = input(candidate, 'verification/roots.json')
    baseline_roots_path = input(root, BASELINE + '/verification/roots.json')
    raise 'Published roots changed' unless sha(baseline_roots_path) == BASELINE_ROOTS_SHA256
    old_roots = JSON.parse(File.read(baseline_roots_path))
    raise 'Published root inventory count differs' unless old_roots.length == BASELINE_ROOT_COUNT
    by_name = roots.to_h { |t| [t.fetch('declaration'), t] }
    raise 'Published root identity removed or changed' unless old_roots.all? { |t| by_name[t.fetch('declaration')] == t }
    baseline_pins = PINS.to_h { |p| [p, sha(input(root, BASELINE + '/' + p))] }
    raise 'Published dependency pins changed' unless baseline_pins.all? { |p, h| gate.sources.fetch(p) == h }
    environment_path = input(task, 'CANDIDATE_ENVIRONMENT.json')
    environment = JSON.parse(File.read(environment_path))
    raise 'Public source map/environment pin mismatch' unless environment.fetch('pins') == baseline_pins
    # current.json's eventual whole-audit pointer contains the hash of this run's
    # bundle. Bind its source-selection projection, not that circular future hash.
    # The actual current.json bytes ARE bound for the duration of each parent run.
    selection = gate.index.slice('format', 'release_version', 'sources', 'roots',
      'contracts', 'completed_checkpoints').merge('source_update_present' => true)
    observed = reader.observed.sort.to_h
    registered_reads = observed.reject { |path, _| path == 'verification/current.json' }
    catalogues = CATALOGUES.to_h { |p| [p, registered_reads.fetch(p)] }
    bindings = observed.to_h { |p, h| [input(candidate, p), h] }
    code.each { |p, h| bindings[input(candidate, p)] = h }
    bindings[baseline_roots_path] = BASELINE_ROOTS_SHA256
    baseline_pins.each { |p, h| bindings[input(root, BASELINE + '/' + p)] = h }
    bindings[environment_path] = sha(environment_path)
    unchanged!(bindings)
    {task: task, root: root, candidate: candidate, roots: roots, sources: gate.sources,
      selection: selection, catalogues: catalogues, collector_inputs: registered_reads,
      collector_code: code, bindings: bindings, environment: environment,
      roots_sha256: sha(roots_path), baseline_pins: baseline_pins,
      source_map_sha256: registered_reads.fetch('verification/release-candidate/SOURCE_HASHES.json')}
  end

  def self.manifest(roots)
    {'schema_version' => 1, 'id' => 'whole-public-root-audit', 'mode' => 'full',
      'definitions' => true, 'allowed_axioms' => AXIOMS, 'boundaries' => [],
      'imports' => ['Atlas.Audit'], 'targets' => roots}
  end

  def self.producer_bindings(task, root)
    {'verify' => ['task', 'verify.rb'], 'monitor' => ['task', 'monitor.rb'],
      'public_helper' => ['task', 'public_audit_support.rb'],
      'public_builder' => ['task', 'build-public-audit-registry.rb'],
      'policy' => ['root', 'verification/tools/policy.rb']}.to_h do |name, (base, path)|
      [name, {'base' => base, 'path' => path, 'sha256' => sha(input(base == 'task' ? task : root, path))}]
    end
  end

  def self.registry(snapshot, manifest_bytes)
    s = snapshot
    {'format' => 1, 'protocol' => PROTOCOL,
      'registration_status' => 'proposal-parent-must-install',
      'manifest' => {'path' => MANIFEST_PATH, 'sha256' => Digest::SHA256.hexdigest(manifest_bytes)},
      'roots' => {'path' => 'verification/roots.json', 'sha256' => s[:roots_sha256], 'count' => s[:roots].size},
      'source_hashes' => {'path' => 'verification/release-candidate/SOURCE_HASHES.json', 'sha256' => s[:source_map_sha256]},
      'catalogues' => s[:catalogues], 'selection_context' => s[:selection],
      'collector_inputs' => s[:collector_inputs], 'collector_code' => s[:collector_code],
      'environment' => {'path' => 'CANDIDATE_ENVIRONMENT.json', 'sha256' => sha(s[:task] + '/CANDIDATE_ENVIRONMENT.json')},
      'baseline_roots' => {'path' => BASELINE + '/verification/roots.json',
        'sha256' => BASELINE_ROOTS_SHA256, 'count' => BASELINE_ROOT_COUNT},
      'baseline_pins' => s[:baseline_pins], 'producer_bindings' => producer_bindings(s[:task], s[:root])}
  end

  # Parent calls only inside its existing v3 lease/watchdog/immutability region.
  def self.load_registered!(task:, root:, candidate:, registry_path:, manifest_path:, sources:, environment:, guard:)
    raise 'Missing parent immutability callback' unless guard.respond_to?(:call)
    guard.call
    task = File.expand_path(task); root = File.expand_path(root)
    raise 'Wrong candidate' unless File.expand_path(candidate) == task + '/candidate'
    raise 'Wrong separate public registry' unless File.expand_path(registry_path) == task + '/PUBLIC_AUDIT_REGISTRY.json'
    registry_path = input(task, 'PUBLIC_AUDIT_REGISTRY.json')
    raw_registry = File.binread(registry_path); registered = JSON.parse(raw_registry)
    raise 'Unreviewed public registration' unless registered['registration_status'] == 'registered-parent-reviewed'
    snapshot = snapshot(task: task, root: root)
    expected_manifest = manifest(snapshot[:roots]); expected_bytes = json_bytes(expected_manifest)
    expected_registry = registry(snapshot, expected_bytes).merge('registration_status' => 'registered-parent-reviewed')
    raise 'Public registration is stale or not exact' unless registered == expected_registry
    registered_manifest = input(task, registered.fetch('manifest').fetch('path'))
    raise 'Unregistered public manifest path' unless File.expand_path(manifest_path) == registered_manifest
    raise 'Public manifest bytes differ' unless File.binread(registered_manifest) == expected_bytes
    raise 'Parent source/environment binding differs' unless sources == snapshot[:sources] && environment == snapshot[:environment]
    helper = input(task, registered.fetch('producer_bindings').fetch('public_helper').fetch('path'))
    raise 'Public helper is not the registered helper' unless File.realpath(helper) == File.realpath(__FILE__)
    snapshot[:bindings][registry_path] = Digest::SHA256.hexdigest(raw_registry)
    snapshot[:bindings][registered_manifest] = Digest::SHA256.hexdigest(expected_bytes)
    registered.fetch('producer_bindings').each_value do |p|
      snapshot[:bindings][input(p['base'] == 'task' ? task : root, p.fetch('path'))] = p.fetch('sha256')
    end
    guard.call; unchanged!(snapshot[:bindings])
    snapshot.merge(manifest: expected_manifest, registry: registered, registry_bytes: raw_registry,
      registry_sha256: Digest::SHA256.hexdigest(raw_registry), manifest_sha256: Digest::SHA256.hexdigest(expected_bytes))
  end

  def self.archive!(context:, stage:)
    c = context; bindings = {}
    copies = {
      'PUBLIC_AUDIT_REGISTRY.json' => c[:task] + '/PUBLIC_AUDIT_REGISTRY.json',
      'roots.json' => c[:candidate] + '/verification/roots.json',
      'PUBLISHED_ROOTS.json' => c[:root] + '/' + BASELINE + '/verification/roots.json',
      'public_audit_support.rb' => c[:task] + '/public_audit_support.rb',
      'PUBLIC_INPUTS/verification/current.json' => c[:candidate] + '/verification/current.json'
    }
    (CATALOGUES + ['verification/release-candidate/SOURCE_HASHES.json']).each do |p|
      copies['PUBLIC_INPUTS/' + p] = c[:candidate] + '/' + p
    end
    COLLECTOR_CODE.each { |p| copies['PUBLIC_COLLECTOR_CODE/' + p] = c[:candidate] + '/' + p }
    copies.each do |relative, source|
      data = File.binread(source); digest = Digest::SHA256.hexdigest(data)
      raise 'Public archive source changed' unless c[:bindings].fetch(source) == digest
      bindings[write_new(stage, relative, data)] = digest
    end
    {'PUBLIC_COLLECTOR_INPUTS.json' => c[:collector_inputs],
      'PUBLIC_SELECTION_CONTEXT.json' => c[:selection], 'PUBLISHED_PINS.json' => c[:baseline_pins]}.each do |relative, value|
      data = json_bytes(value)
      bindings[write_new(stage, relative, data)] = Digest::SHA256.hexdigest(data)
    end
    unchanged!(c[:bindings])
    bindings
  end

  def self.declarations_match!(context, declarations)
    expected = context.fetch(:roots)
    raise 'Incomplete public extraction' unless declarations.map { |d| d.fetch('declaration') } == expected.map { |r| r.fetch('declaration') }
    declarations.zip(expected).each do |actual, target|
      raise 'Wrong actual public defining module' unless actual.fetch('module') == target.fetch('module')
    end
  end
end
