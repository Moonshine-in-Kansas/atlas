#!/usr/bin/env ruby
# UNEXECUTED SOURCE-ONLY PROPOSAL. Parent supplies reviewed, completed inputs.
# No verifier, compiler, policy evaluator, cache validator or subprocess is run.
require 'json'
require 'digest'
require 'fileutils'
require 'time'
require 'set'

module AtlasWholeCollector
  ROOT = '/home/gerald/atlas'.freeze
  TASK = (ROOT + '/claude/release-update-v1.2-20261030').freeze
  CANDIDATE = (TASK + '/candidate').freeze
  PROTOCOL = 'atlas-whole-public-four-step-collection-v1'.freeze
  AXIOMS = %w[propext Classical.choice Quot.sound].freeze
  PINS = %w[lean-toolchain lakefile.toml lake-manifest.json].freeze
  ROLES = %w[cache_current atlas_root audit_root public_audit].freeze
  INPUTS = %w[source_hashes roots object_bindings public_registry merged_sources].freeze
  INPUT_PATHS = {'source_hashes' => 'candidate/verification/release-candidate/SOURCE_HASHES.json',
    'roots' => 'candidate/verification/roots.json', 'object_bindings' => 'OBJECT_BINDINGS.json',
    'public_registry' => 'PUBLIC_AUDIT_REGISTRY.json', 'merged_sources' => 'MERGED_SOURCES.json'}.freeze
  INTERFACES = %w[receipt_adapter parent_receipts release_evidence release_metadata].freeze
  # Frozen reviewed interfaces. A later interface revision requires an explicit
  # successor proposal; a different hash in a selection cannot load new code.
  INTERFACE_SHA256 = {
    'receipt_adapter' => '51c6f74bd1c36e16a44b34383be629644b8fcabf1afa5a999b82c7a0627d6301',
    'parent_receipts' => 'e2e8f1239765c67fa1e369daa8101aeae6a43c0b30b7aef02f83f45db85a658f',
    'release_evidence' => 'e094fb541c79939516f86b66a71f1f5e23676b5fcabcaa9c96a5ee3ccc78d165',
    'release_metadata' => 'd47d79090bff98cf64a390df8daf19ca2f8ef0bbf3d12e2771aaa8da3f66cc95'
  }.freeze
  CACHE_MAPS = %w[SOURCE_HASHES.json SOURCE_HASHES_AFTER.json CACHE_SOURCE_HASHES.json
    CACHE_ARTIFACTS.json CACHE_ARTIFACTS_AFTER.json OBJECT_BINDINGS.json].freeze
  FIELDS = %w[source source_sha256 object object_sha256 basis evidence].freeze

  class UniqueObject < Hash
    def []=(key, value)
      raise "Duplicate JSON key: #{key}" if key?(key)
      super
    end
  end

  def self.parse(bytes) = JSON.parse(bytes, object_class: UniqueObject, allow_duplicate_key: false)
  def self.encode(value) = JSON.pretty_generate(value) + "\n"
  def self.sha(path) = Digest::SHA256.file(path).hexdigest
  def self.eq(actual, expected, message)
    raise message unless actual == expected
  end
  def self.hash!(digest)
    raise 'Invalid explicit SHA256' unless digest.is_a?(String) && digest.match?(/\A[0-9a-f]{64}\z/)
  end
  def self.relative!(path)
    raise 'Unsafe relative member' unless path.is_a?(String) && !path.empty? &&
      !path.start_with?('/') && !path.match?(/[\x00-\x1f\\]/) &&
      path.split('/').none? { |s| s.empty? || %w[. ..].include?(s) }
    path
  end
  def self.path(base, relative)
    relative!(relative)
    full = File.expand_path(relative, base)
    cursor = '/'
    full.split('/').reject(&:empty?).each do |part|
      cursor = File.join(cursor, part)
      raise 'Symlinked selection/artifact path' if File.symlink?(cursor)
    end
    raise "Missing regular input: #{full}" unless File.file?(full)
    full
  end

  class Collector
    def initialize(selection, digest, output)
      @selection_path = File.expand_path(selection)
      raise 'Selection must be inside parent task' unless @selection_path.start_with?(TASK + '/')
      @output = File.expand_path(output)
      raise 'Output must be a new immediate whole-public-bundles child' unless
        File.dirname(@output) == TASK + '/whole-public-bundles'
      raise 'Preserve previous collection' if File.exist?(@output) || File.symlink?(@output)
      raise 'Symlinked bundle output parent' if File.symlink?(File.dirname(@output))
      @bindings = {}; @parents = {}; @stages = {}; @inventories = {}; @adapters = {}
      @uncompressed = {}; @aliases = []
      @selection_bytes = read(TASK, @selection_path.delete_prefix(TASK + '/'), digest)
      @selection = AtlasWholeCollector.parse(@selection_bytes)
      eq(@selection.keys.sort, %w[format protocol authorized_not_before inputs interfaces receipts].sort,
        'Unknown or missing selection fields')
      eq(@selection.fetch('format'), 1, 'Wrong selection format')
      eq(@selection.fetch('protocol'), PROTOCOL, 'Wrong selection protocol')
      eq(@selection.fetch('receipts').keys.sort, ROLES.sort, 'Select exactly four parent receipts')
      eq(@selection.fetch('inputs').keys.sort, INPUTS.sort, 'Incomplete explicit final input selection')
      eq(@selection.fetch('interfaces').keys.sort, INTERFACES.sort, 'Incomplete reviewed pure-helper selection')
      @authorized = Time.iso8601(@selection.fetch('authorized_not_before'))
      raise 'Authorization predates the release update' if @authorized < Time.iso8601('2026-10-30T00:00:00Z')
    end

    def eq(a, b, message) = AtlasWholeCollector.eq(a, b, message)
    def pin(base, relative, expected = nil)
      full = AtlasWholeCollector.path(base, relative)
      digest = AtlasWholeCollector.sha(full)
      if expected
        AtlasWholeCollector.hash!(expected)
        eq(digest, expected, "Explicit input binding differs: #{relative}")
      end
      eq(digest, @bindings[full], 'Input changed while collecting') if @bindings.key?(full)
      @bindings[full] = digest
      full
    end
    def read(base, relative, expected = nil)
      full = pin(base, relative, expected); data = File.binread(full)
      eq(Digest::SHA256.hexdigest(data), @bindings.fetch(full), 'Input changed during read')
      data
    end
    def json(base, relative, expected = nil) = AtlasWholeCollector.parse(read(base, relative, expected))
    def selected_input(name)
      row = @selection.fetch('inputs').fetch(name)
      eq(row.fetch('path'), INPUT_PATHS.fetch(name), 'Final input must be the actual canonical parent file')
      AtlasWholeCollector.hash!(row.fetch('sha256'))
      json(TASK, row.fetch('path'), row.fetch('sha256'))
    end
    def generated(relative, object)
      AtlasWholeCollector.relative!(relative)
      raise 'Plaintext dependency graph forbidden' if File.basename(relative) == 'dependencies.jsonl'
      full = @output + '/' + relative
      raise 'Preserve previous output member' if File.exist?(full) || File.symlink?(full)
      FileUtils.mkdir_p(File.dirname(full))
      bytes = object.is_a?(String) ? object : AtlasWholeCollector.encode(object)
      File.open(full, File::WRONLY | File::CREAT | File::EXCL, 0o644) { |f| f.binmode; f.write(bytes) }
    end
    def copy(source, destination, expected)
      AtlasWholeCollector.relative!(destination)
      raise 'Plaintext dependency graph forbidden' if File.basename(destination) == 'dependencies.jsonl'
      raise 'Compiled artifact forbidden in portable bundle' if destination.match?(/\.(?:olean|ilean|o|a|so)\z/)
      full = @output + '/' + destination
      raise 'Output member already exists' if File.exist?(full) || File.symlink?(full)
      eq(AtlasWholeCollector.sha(source), expected, 'Changed source of portable copy')
      FileUtils.mkdir_p(File.dirname(full)); FileUtils.copy_file(source, full)
      eq(AtlasWholeCollector.sha(full), expected, 'Portable copy differs from original')
    end

    def load_interfaces!
      @tool_paths = @selection.fetch('interfaces').to_h do |role, row|
        eq(row.fetch('sha256'), INTERFACE_SHA256.fetch(role), 'Interface differs from this frozen reviewed schema')
        [role, pin(TASK, row.fetch('path'), row.fetch('sha256'))]
      end
      adapter = @tool_paths.fetch('receipt_adapter')
      eq(@tool_paths.fetch('parent_receipts'), File.dirname(adapter) + '/successor/verification/parent_receipts.rb',
        'Adapter must load the exact selected parent-receipt helper')
      # Only the pure adapter/receipt reader is loaded. The gate and producer
      # code are hash-bound interface references, never executed by collection.
      require adapter
      eq(AtlasParentReceipts::STATUSES.fetch('cache-current'), 'passed-current-cache-integrity',
        'Select the reviewed cache-current consumer successor')
      raise 'Select the compression-aware adapter' unless AtlasVerifyReceiptAdapter.respond_to?(:export_plan)
      eq(File.realpath(AtlasParentReceipts.method(:validate).source_location.first), @tool_paths['parent_receipts'],
        'A different parent receipt implementation was preloaded')
      eq(File.realpath(AtlasVerifyReceiptAdapter.method(:adapt).source_location.first), adapter,
        'A different receipt adapter was preloaded')
    end

    def current_inputs!
      @sources = selected_input('source_hashes'); @roots = selected_input('roots')
      @objects = selected_input('object_bindings'); @public = selected_input('public_registry')
      @merged = selected_input('merged_sources')
      expected_paths = (Dir.glob(CANDIDATE + '/Atlas/**/*.lean') +
        ['Atlas.lean', *PINS].map { |p| CANDIDATE + '/' + p }).map { |p| p.delete_prefix(CANDIDATE + '/') }.sort
      eq(@sources.keys.sort, expected_paths, 'Final source/pin map has missing or extra members')
      @sources.each { |p, h| pin(CANDIDATE, p, h) }
      eq(@roots, @roots.sort_by { |r| r.fetch('declaration') }, 'Public roots must retain exact gate order')
      names = @roots.map { |r| r.fetch('declaration') }
      raise 'Empty or repeated public roots' if names.empty? || names.uniq != names
      raise 'Wrong public root layout' unless @roots.all? { |r|
        r.keys.sort == %w[declaration kind module] && r['kind'] == 'any' }
      eq(@public.values_at('format', 'protocol', 'registration_status'),
        [1, 'atlas-registered-whole-public-audit-v1', 'registered-parent-reviewed'], 'Unregistered public selection')
      eq(@public.fetch('roots').fetch('count'), @roots.size, 'Public count differs from actual selection')
      eq(@public['roots']['sha256'], @selection['inputs']['roots']['sha256'], 'Public roots byte binding differs')
      eq(@public['source_hashes']['sha256'], @selection['inputs']['source_hashes']['sha256'], 'Public source-map binding differs')
      @public.fetch('catalogues').each { |p, h| pin(CANDIDATE, p, h) }
      modules = @sources.keys.grep(/\.lean\z/).map { |p| p.delete_suffix('.lean').tr('/', '.') }.sort
      eq(@objects.keys.sort, modules, 'Current object provenance inventory differs')
      @cache_objects = @objects.to_h do |mod, row|
        eq(row.fetch('source'), mod.tr('.', '/') + '.lean', 'Current object source identity differs')
        eq(row.fetch('object'), '.lake/build/lib/lean/' + mod.tr('.', '/') + '.olean', 'Current object path differs')
        eq(row.fetch('source_sha256'), @sources.fetch(row['source']), 'Current object source is stale')
        AtlasWholeCollector.hash!(row.fetch('object_sha256'))
        [row['object'], row['object_sha256']]
      end
      @revisions = json(CANDIDATE, 'lake-manifest.json', @sources.fetch('lake-manifest.json')).fetch('packages')
        .to_h { |p| [p.fetch('name'), p.fetch('rev')] }
    end

    def validate_parents!
      @selection.fetch('receipts').each do |role, choice|
        result = choice.fetch('result'); relative = result.fetch('path')
        raise 'Select a genuine parent verification-run RESULT' unless relative.match?(%r{\Averification-runs/[^/]+/RESULT\.json\z})
        AtlasWholeCollector.hash!(result.fetch('sha256'))
        AtlasWholeCollector.hash!(choice.fetch('inventory_sha256'))
        result_path = pin(TASK, relative, result.fetch('sha256'))
        stage = File.dirname(result_path); reader = AtlasVerifyReceiptAdapter::Reader.new(stage)
        inventory = reader.inventory
        eq(Digest::SHA256.hexdigest(AtlasWholeCollector.encode(inventory.sort.to_h)),
          choice.fetch('inventory_sha256'), 'Explicit complete original stage inventory differs')
        inventory.each { |p, h| pin(stage, p, h) }
        checked = AtlasParentReceipts.validate(reader, 'RESULT.json', @sources,
          normal: %w[atlas_root audit_root].include?(role), full: role == 'public_audit', current_objects: @objects)
        export = AtlasVerifyReceiptAdapter.export_plan(reader, checked, inventory: inventory, prefix: 'original')
        raise 'Retained plaintext graph would enter portable output' if export.fetch('retained_inventory').keys.any? { |p|
          File.basename(p) == 'dependencies.jsonl' }
        retained_graphs = export.fetch('retained_inventory').keys.select { |p| File.basename(p) == 'dependencies.jsonl.gz' }
        eq(retained_graphs, role == 'public_audit' ? ['dependencies.jsonl.gz'] : [], 'Unexpected extraction graph in a nonpublic step')
        row = checked.fetch(:result)
        eq(row.fetch('candidate'), CANDIDATE, 'Parent checked a different candidate')
        raise 'Parent has not passed its outer final guard' unless row.fetch('final_immutability_verified') == true
        raise 'Parent result predates authorization' if Time.iso8601(row.fetch('started_utc')) < @authorized
        eq(row.fetch('dependency_revisions'), @revisions, 'Parent dependency pins differ')
        eq(reader.json('SOURCE_HASHES.json'), @sources, 'Whole step source snapshot differs')
        eq(row.fetch('integration_registry_sha256'), @selection['inputs']['merged_sources']['sha256'],
          'Whole step used another final complete merged registry')
        case role
        when 'cache_current'
          eq(row.values_at('mode', 'status'), %w[cache-current passed-current-cache-integrity], 'Wrong current-cache parent')
        when 'atlas_root', 'audit_root'
          mod = role == 'atlas_root' ? 'Atlas' : 'Atlas.Audit'
          eq(row.values_at('mode', 'name'), ['root', mod], 'Wrong fresh root receipt')
          eq(@objects.fetch(mod).fetch('evidence'), relative, 'Selected root is not the current object provenance')
        when 'public_audit'
          eq(row.values_at('mode', 'status'), %w[audit-public passed-full-canonical-dependency-audit], 'Wrong whole public parent')
          eq(row.fetch('whole_public_root_audit'), true, 'Parent did not identify the whole public audit')
          eq(row.fetch('public_registry_sha256'), @selection['inputs']['public_registry']['sha256'], 'Parent public registry differs')
          eq(row.fetch('public_roots_sha256'), @selection['inputs']['roots']['sha256'], 'Parent public roots byte binding differs')
          eq(reader.json('PUBLIC_AUDIT_REGISTRY.json'), @public, 'Archived public registry differs')
          eq(reader.json('roots.json'), @roots, 'Archived public roots differ')
          manifest = reader.json('MANIFEST.json')
          eq(reader.sha('MANIFEST.json'), @public.fetch('manifest').fetch('sha256'), 'Public manifest differs from its exact registration')
          eq(manifest.keys.sort, %w[schema_version id mode definitions allowed_axioms boundaries imports targets].sort,
            'Public manifest has missing fields or additional exclusions')
          eq(manifest.values_at('schema_version', 'id'), [1, 'whole-public-root-audit'], 'Wrong public manifest identity')
          eq(manifest.fetch('targets'), @roots, 'Full extraction omits exact selected public roots')
          eq(manifest.values_at('imports', 'mode', 'definitions', 'boundaries'), [['Atlas.Audit'], 'full', true, []], 'Public manifest is not neutral full extraction')
          eq(manifest.fetch('allowed_axioms').sort, AXIOMS.sort, 'Public axiom policy differs')
          eq(reader.json('SOURCE_HASHES_AFTER.json'), @sources, 'Public final source map differs')
          AtlasParentReceipts.guarded(reader, 'PUBLIC_AUDIT_REGISTRY.json', checked.fetch(:guarded_bindings))
          imported = reader.json('IMPORTED_OBJECTS.json')
          imported.each do |mod, binding|
            eq(FIELDS.map { |k| binding.fetch(k) }, FIELDS.map { |k| @objects.fetch(mod).fetch(k) }, 'Public imported object differs from the current cache')
          end
          reader.json('PROJECT_COMPILED_ARTIFACTS.json').each do |p, h|
            eq(h, @cache_objects.fetch(p), 'Public graph object differs from validated cache')
          end
        end
        @stages[role] = reader; @inventories[role] = inventory; @parents[role] = checked
      end
      raise 'One parent receipt reused for distinct steps' unless @stages.values.map(&:root).uniq.size == 4
      cache = @parents.fetch('cache_current').fetch(:result)
      public = @parents.fetch('public_audit').fetch(:result)
      %w[atlas_root audit_root].each do |role|
        finished = Time.iso8601(@parents[role][:result].fetch('finished_utc'))
        raise 'Cache/public check predates the selected final root proof' unless
          finished <= Time.iso8601(cache.fetch('started_utc')) && finished <= Time.iso8601(public.fetch('started_utc'))
      end
      raise 'Selected cache/public parent runs overlap the serial lease' unless
        Time.iso8601(cache.fetch('finished_utc')) <= Time.iso8601(public.fetch('started_utc')) ||
        Time.iso8601(public.fetch('finished_utc')) <= Time.iso8601(cache.fetch('started_utc'))
    end

    def cache_payload!
      reader = @stages.fetch('cache_current'); outer = @parents['cache_current'][:result]
      eq(outer.fetch('cache_binding'), 'cache/CACHE_BINDING.json', 'Unexpected cache child pointer')
      eq(reader.sha(outer['cache_binding']), outer.fetch('cache_binding_sha256'), 'Cache child binding changed')
      child = reader.json(outer['cache_binding'])
      eq(child.fetch('status'), 'validated-current-cache-integrity-child-result', 'No actual current-cache validation')
      %w[sources_unchanged cache_artifacts_unchanged].each do |key|
        eq(outer.fetch(key), true, 'Outer cache integrity flag missing')
        eq(child.fetch(key), true, 'Child cache integrity flag missing')
      end
      %w[fresh_whole_project_rebuild fresh_project_rebuild independent_replay new_proof_build new_full_dependency_audit].each do |key|
        eq(child.fetch(key), false, 'Current cache cannot claim new proof/replay')
      end
      eq(child.fetch('current_cache_integrity_validation_performed'), true, 'Missing actual integrity work')
      child.fetch('files').each do |p, h|
        AtlasWholeCollector.relative!(p); eq(reader.sha('cache/' + p), h, 'Cache child payload changed')
      end
      CACHE_MAPS.each { |p| child.fetch('files').fetch(p) }
      %w[SOURCE_HASHES.json SOURCE_HASHES_AFTER.json CACHE_SOURCE_HASHES.json].each do |p|
        eq(reader.json('cache/' + p), @sources, 'Current cache map differs from exact final sources')
      end
      %w[CACHE_ARTIFACTS.json CACHE_ARTIFACTS_AFTER.json].each do |p|
        eq(reader.json('cache/' + p), @cache_objects, 'Actual before/after cache snapshot differs')
      end
      eq(reader.json('cache/OBJECT_BINDINGS.json'), @objects, 'Cache provenance differs from selected current object map')
      eq(outer.fetch('object_bindings_sha256'), reader.sha('cache/OBJECT_BINDINGS.json'), 'Outer object map binding differs')
      eq(outer.fetch('cache_artifacts_sha256'), reader.sha('cache/CACHE_ARTIFACTS.json'), 'Outer cache map binding differs')
      @cache_child = child
    end

    def adapt!
      FileUtils.mkdir_p(@output + '/steps')
      ROLES.each do |role|
        reader = @stages.fetch(role); prefix = 'steps/' + role
        binding = AtlasVerifyReceiptAdapter.adapt(reader.root, @output + '/' + prefix, @sources, current_objects: @objects)
        eq(binding.fetch('original_inventory'), @inventories.fetch(role), 'Adapter original inventory changed')
        @adapters[role] = binding
        sub = AtlasVerifyReceiptAdapter::Reader.new(@output + '/' + prefix)
        sub.json('BUNDLE.json').fetch('uncompressed_hashes').each { |p, h| @uncompressed[prefix + '/' + p] = h }
      end
    end

    def prefixed_row(role, key)
      row = @adapters.fetch(role).fetch(key)
      paths = %w[parent_result record log checkpoint roots result declarations dependencies]
      row.to_h { |k, v| [k, paths.include?(k) ? 'steps/' + role + '/' + v : v] }
    end
    def alias_copy(role, member, output)
      source = @output + '/steps/' + role + '/original/' + member
      hash = @stages.fetch(role).sha(member)
      copy(source, output, hash)
      @aliases << {'alias' => output, 'original' => 'steps/' + role + '/original/' + member, 'sha256' => hash}
    end

    def bundle_members!
      @steps = [prefixed_row('cache_current', 'cache_step').merge('name' => 'cache-hashes'),
        prefixed_row('atlas_root', 'normal_proof_row').merge('name' => 'root-elaboration'),
        prefixed_row('audit_root', 'normal_proof_row').merge('name' => 'audit-root-elaboration'),
        prefixed_row('public_audit', 'scope_artifacts').merge('name' => 'full-dependency-extraction')]
      @steps.zip(ROLES).each { |step, role| step['status'] = @parents.fetch(role).fetch(:process).fetch('status') }
      # These are real after maps from two original producers, never a renamed
      # before snapshot or a collector-invented integrity measurement.
      %w[SOURCE_HASHES.json SOURCE_HASHES_AFTER.json roots.json PUBLIC_AUDIT_REGISTRY.json].each do |p|
        alias_copy('public_audit', p, p)
      end
      %w[CACHE_SOURCE_HASHES.json CACHE_ARTIFACTS.json CACHE_ARTIFACTS_AFTER.json OBJECT_BINDINGS.json].each do |p|
        alias_copy('cache_current', 'cache/' + p, p)
      end
      alias_copy('public_audit', 'declarations.jsonl', 'declarations.jsonl')
      log = @parents['public_audit'].fetch(:log_path)
      alias_copy('public_audit', log, 'full-dependency-extraction.log.gz')
      @uncompressed['full-dependency-extraction.log'] = @parents['public_audit'].fetch(:plain_sha256)
      PINS.each { |p| copy(pin(CANDIDATE, p, @sources.fetch(p)), 'PINS/' + p, @sources[p]) }
      generated('SELECTION.json', @selection_bytes)
      copy(__FILE__, 'COLLECTOR_TOOLS/collect-whole.rb', @bindings.fetch(File.expand_path(__FILE__)))
      @tool_paths.each { |role, p| copy(p, 'COLLECTOR_TOOLS/' + role + '.rb', @bindings.fetch(p)) }
      generated('ALIASES.json', {'format' => 1, 'entries' => @aliases})
      generated('COLLECTION_BINDINGS.json', {'format' => 1, 'selection_sha256' => Digest::SHA256.hexdigest(@selection_bytes),
        'original_results' => @selection.fetch('receipts'), 'inputs' => @selection.fetch('inputs'),
        'interfaces' => @selection.fetch('interfaces'), 'collector_sha256' => AtlasWholeCollector.sha(__FILE__),
        'compression_rule' => 'One original SHA-verified gzip graph; no plaintext graph export; private originals unchanged.'})
    end

    def recheck!
      @bindings.each { |p, h| eq(AtlasWholeCollector.sha(p), h, 'Bound input changed before bundle commit') }
      @stages.each { |role, reader| eq(reader.inventory, @inventories.fetch(role), 'Original stage changed before bundle commit') }
      current_paths = (Dir.glob(CANDIDATE + '/Atlas/**/*.lean') + ['Atlas.lean', *PINS].map { |p| CANDIDATE + '/' + p })
        .map { |p| p.delete_prefix(CANDIDATE + '/') }.sort
      eq(current_paths, @sources.keys.sort, 'Source membership changed during collection')
    end

    def commit!
      full = @parents['public_audit'][:result]; cache = @parents['cache_current'][:result]
      results = @parents.values.map { |p| p.fetch(:result) }
      record = {'format' => 1, 'status' => 'passed-source-bound-cache-audit',
        'started_utc' => results.min_by { |r| Time.iso8601(r.fetch('started_utc')) }.fetch('started_utc'),
        'finished_utc' => results.max_by { |r| Time.iso8601(r.fetch('finished_utc')) }.fetch('finished_utc'),
        'collected_utc' => Time.now.utc.iso8601,
        'fresh_project_rebuild' => false, 'independent_replay' => false,
        'sources_unchanged' => full.fetch('sources_unchanged'),
        'cache_artifacts_unchanged' => cache.fetch('cache_artifacts_unchanged'),
        'roots' => @roots.size, 'dependency_nodes' => full.fetch('dependency_nodes'),
        'axioms' => full.fetch('allowed_axioms'), 'dependency_revisions' => @revisions,
        'object_bindings' => 'OBJECT_BINDINGS.json', 'steps' => @steps,
        'cache_integrity_interval' => {'started_utc' => cache.fetch('started_utc'), 'finished_utc' => cache.fetch('finished_utc'),
          'parent_result' => @steps.first.fetch('parent_result'), 'parent_result_sha256' => @steps.first.fetch('parent_result_sha256'),
          'child_binding_sha256' => cache.fetch('cache_binding_sha256')},
        'scope' => 'Collected genuine current cache integrity, two fresh roots and full public dependency audit. Cache before/after are the original integrity-run snapshots; no later cache snapshot is invented.',
        'additions_policies_replaced' => false, 'new_proof_or_audit_performed_by_collector' => false}
      generated('RESULT.json', record)
      reader = AtlasVerifyReceiptAdapter::Reader.new(@output)
      inventory = reader.inventory
      raise 'Plaintext graph was exported' if inventory.keys.any? { |p| File.basename(p) == 'dependencies.jsonl' }
      graphs = inventory.keys.select { |p| File.basename(p) == 'dependencies.jsonl.gz' }
      eq(graphs, [@steps.last.fetch('dependencies')], 'Portable bundle must contain exactly one gzip graph')
      AtlasVerifyReceiptAdapter.check_public_sizes(reader, inventory.keys)
      recheck!
      generated('BUNDLE.json', {'format' => 1, 'files' => inventory, 'uncompressed_hashes' => @uncompressed.sort.to_h})
      {'status' => 'collected-four-genuine-parent-steps', 'directory' => @output,
        'bundle_sha256' => AtlasWholeCollector.sha(@output + '/BUNDLE.json'), 'roots' => @roots.size,
        'new_proof_or_audit_performed' => false}
    end

    def run
      # Collection is serial metadata work under the same queue lease. No
      # process monitor or proof worker is started by this collector.
      File.open(ROOT + '/verification/chevalley/.runner.lock', File::RDWR) do |lease|
        raise 'Parent verification queue is active' unless lease.flock(File::LOCK_EX | File::LOCK_NB)
        begin
          pin(File.dirname(__FILE__), File.basename(__FILE__))
          load_interfaces!; current_inputs!; validate_parents!; cache_payload!
          raise 'Output appeared during validation' if File.exist?(@output) || File.symlink?(@output)
          adapt!; bundle_members!; commit!
        ensure
          lease.flock(File::LOCK_UN)
        end
      end
    end
  end
end

if $PROGRAM_NAME == __FILE__
  begin
    abort 'Usage: collect-whole.rb SELECTION.json SELECTION_SHA256 NEW_TASK_BUNDLE_DIRECTORY' unless ARGV.size == 3
    puts JSON.pretty_generate(AtlasWholeCollector::Collector.new(*ARGV).run)
  rescue StandardError => e
    warn "Whole bundle collection refused: #{e.message}"
    exit 1
  end
end
