require 'json'
require 'digest'
require 'fileutils'
require 'time'
require 'zlib'
require 'open3'
require_relative 'monitor'
require '/home/gerald/atlas/verification/tools/policy'

ROOT = '/home/gerald/atlas'
TASK = __dir__
CANDIDATE = TASK + '/candidate'
LEAN = '/home/gerald/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean'
mode, name = ARGV
abort 'Usage: verify.rb cache-hashes | cache-current | build MODULE | audit MANIFEST | audit-batch REGISTERED_MANIFEST | audit-public REGISTERED_MANIFEST | root MODULE' unless
  (%w[cache-hashes cache-current].include?(mode) && ARGV.size == 1) || (%w[build audit audit-batch audit-public root].include?(mode) && ARGV.size == 2)
label = name ? File.basename(name, '.json').gsub(/[^A-Za-z0-9_.-]/, '_') : (mode == 'cache-current' ? 'current' : 'baseline')
OUT = TASK + '/verification-runs/' + Time.now.utc.strftime('%Y%m%dT%H%M%S') + '-' + mode + '-' + label
raise 'Preserve previous run' if File.exist?(OUT)
FileUtils.mkdir_p(OUT)
sha = ->(path) { Digest::SHA256.file(path).hexdigest }
source_map = lambda do
  (Dir.glob(CANDIDATE + '/Atlas/**/*.lean') + %w[Atlas.lean lean-toolchain lakefile.toml lake-manifest.json].map { |p| CANDIDATE + '/' + p }).sort.to_h do |path|
    [path.delete_prefix(CANDIDATE + '/'), sha.call(path)]
  end
end
sources = source_map.call
File.write(OUT + '/SOURCE_HASHES.json', JSON.pretty_generate(sources) + "\n")
record = {started_utc: Time.now.utc.iso8601, status: 'preparing', mode: mode, name: name,
  candidate: CANDIDATE, source_hashes_sha256: sha.call(OUT + '/SOURCE_HASHES.json'),
  tool_sha256: sha.call(__FILE__), monitor_sha256: sha.call(TASK + '/monitor.rb'),
  canonical_package: true, root_integration: mode == 'root',
  fresh_whole_project_rebuild: false, independent_replay: false}
packages = JSON.parse(File.read(CANDIDATE + '/lake-manifest.json')).fetch('packages')
paths = [CANDIDATE + '/.lake/build/lib/lean'] + packages.reverse.map { |p| ROOT + '/.lake/packages/' + p.fetch('name') + '/.lake/build/lib/lean' }
env = {'LEAN_NUM_THREADS' => '2', 'LEAN_PATH' => paths.join(':')}
options = %w[-j1 -M8704 -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3]
class PreparationMemoryStop < StandardError; end
lease = nil
watchdog = nil
process = nil
pending_status = nil
ready_to_commit = false
object_index = nil
object_index_path = nil
new_object_binding = nil
cache_context = nil
used_imports = {}
bound_files = {}
json_inputs = {}
# Memoize evidence reads; the final check rehashes each distinct bound file once.
bind_file = lambda do |path, expected = nil|
  path = File.expand_path(path)
  actual = sha.call(path)
  raise "Changed bound input #{path}" if bound_files.key?(path) && bound_files.fetch(path) != actual
  raise "Input hash mismatch #{path}" if expected && actual != expected
  bound_files[path] = actual
end
read_bound_json = lambda do |path, expected = nil|
  path = File.expand_path(path)
  unless json_inputs.key?(path)
    bytes = File.binread(path)
    digest = Digest::SHA256.hexdigest(bytes)
    raise "Changed bound input #{path}" if bound_files.key?(path) && bound_files.fetch(path) != digest
    bound_files[path] = digest
    json_inputs[path] = JSON.parse(bytes)
  end
  raise "Input hash mismatch #{path}" if expected && bound_files.fetch(path) != expected
  json_inputs.fetch(path)
end
binding_fields = %w[source source_sha256 object object_sha256 basis evidence]
binding_identity = ->(binding) { binding_fields.map { |field| binding.fetch(field) } }
mark_failure = lambda do |error|
  ready_to_commit = false
  if mode == 'cache-current'
    record[:final_immutability_verified] = false
    record[:sources_unchanged] = false
    record[:cache_artifacts_unchanged] = false
  end
  record[:status] = record[:ruby_guard_stop] || error.is_a?(PreparationMemoryStop) ||
    (defined?(process) && process && process[:status] == 'memory-stopped') ? 'memory-stopped' : 'not-passed'
  record[:failure] = error.message.to_s[0, 2048]
end
write_minimal_failure = lambda do
  failure = record.slice(:started_utc, :status, :mode, :name, :candidate, :failure,
    :ruby_guard_stop, :process_receipt, :process_receipt_sha256,
    :source_hashes_sha256, :tool_sha256, :monitor_sha256)
  failure[:finished_utc] = Time.now.utc.iso8601
  failure[:minimal_failure_receipt] = true
  failure[:sources_unchanged] = false
  File.write(OUT + '/RESULT.json', JSON.generate(failure) + "\n")
end
begin
  # Only active work is interruptible. Receipt writing and lease cleanup are not.
  Thread.handle_interrupt(PreparationMemoryStop => :never) do
    begin
      Thread.handle_interrupt(PreparationMemoryStop => :immediate) do
        lease = File.open(ROOT + '/verification/chevalley/.runner.lock', File::RDWR)
        raise 'Another build/audit owns the serial lease' unless lease.flock(File::LOCK_EX | File::LOCK_NB)
        main_thread = Thread.current
        watchdog = Thread.new do
          loop do
            sleep 1
            memory = ReleasePreparationMonitor.memory
            workers = ReleasePreparationMonitor.workers
            self_status = File.read('/proc/self/status')
            self_rss = self_status[/^VmRSS:\s+(\d+)/, 1].to_i * 1024
            if memory.fetch('MemAvailable') < 1024**3 || self_rss >= 9 * 1024**3 ||
                workers.fetch(:combined_rss) >= memory.fetch('MemTotal') * 2 / 3 || workers.fetch(:total_lean) > 4
              record[:ruby_guard_stop] = {memory: memory, workers: workers, supervisor_rss: self_rss}
              main_thread.raise PreparationMemoryStop, 'Memory/worker reserve reached during stage orchestration or audit processing'
              break
            end
          end
        end
        bind_file.call(__FILE__, record.fetch(:tool_sha256))
        bind_file.call(TASK + '/monitor.rb', record.fetch(:monitor_sha256))
        bind_file.call(ROOT + '/verification/tools/policy.rb')
        bind_file.call(OUT + '/SOURCE_HASHES.json', record.fetch(:source_hashes_sha256))
        merged_path = TASK + '/MERGED_SOURCES.json'
        merged_bytes = File.binread(merged_path)
        merged = JSON.parse(merged_bytes)
        File.binwrite(OUT + '/MERGED_SOURCES.json', merged_bytes)
        record[:integration_registry_sha256] = Digest::SHA256.hexdigest(merged_bytes)
        bind_file.call(merged_path, record.fetch(:integration_registry_sha256))
        baseline_sources = read_bound_json.call(TASK + '/BASELINE_EXPORT.json').fetch('files')
        merged.fetch('sources').each do |path, entry|
          raise "Unbound canonical source #{path}" unless sources.fetch(path) == entry.fetch('sha256')
          bind_file.call(ROOT + '/' + entry.fetch('original_source'), entry.fetch('original_sha256'))
        end
        sources.keys.grep(%r{\AAtlas/.*\.lean\z}).each do |path|
          next if merged.fetch('sources').key?(path)
          raise "Unmapped or modified baseline module #{path}" unless baseline_sources[path] == sources.fetch(path)
        end
        environment = read_bound_json.call(TASK + '/CANDIDATE_ENVIRONMENT.json')
        raise 'Candidate pin mismatch' unless environment.fetch('pins').all? { |p, h| sources.fetch(p) == h }
        revisions = {}
        packages.each do |package|
          path = '.lake/packages/' + package.fetch('name')
          git_env = {'GIT_OPTIONAL_LOCKS' => '0'}
          git_env.merge!('GIT_NO_LAZY_FETCH' => '1', 'GIT_TERMINAL_PROMPT' => '0', 'GIT_LFS_SKIP_SMUDGE' => '1') if mode == 'cache-current'
          rev, err, status = Open3.capture3(git_env, 'git', '-C', ROOT + '/' + path, 'rev-parse', 'HEAD')
          raise "Wrong dependency revision: #{path} #{err}" unless status.success? && rev.strip == package.fetch('rev')
          dirty, err, status = Open3.capture3(git_env, 'git', '-C', ROOT + '/' + path, 'status', '--porcelain', '--untracked-files=no')
          raise "Dirty dependency: #{path} #{err}" unless status.success? && dirty.empty?
          revisions[path] = rev.strip
        end
        raise 'Candidate environment revisions differ' unless revisions == environment.fetch('revisions')
        File.write(OUT + '/ENVIRONMENT.json', JSON.pretty_generate(environment) + "\n")
        record[:dependency_revisions] = packages.to_h { |p| [p.fetch('name'), p.fetch('rev')] }
        record[:environment_sha256] = sha.call(OUT + '/ENVIRONMENT.json')
  check_immutable = lambda do
    raise 'Candidate mathematics changed during verification' unless sources == source_map.call
    bound_files.each do |path, expected|
      raise "Bound input changed during verification: #{path}" unless sha.call(path) == expected
    end
    used_imports.each_value do |binding|
      raise 'Imported object changed during verification' unless sha.call(CANDIDATE + '/' + binding.fetch('object')) == binding.fetch('object_sha256')
    end
    if record[:compiled_object]
      raise 'Compiled output changed before finalization' unless
        sha.call(CANDIDATE + '/' + record.fetch(:compiled_object)) == record.fetch(:compiled_sha256)
    end
    AtlasCurrentCacheSupport.immutable!(cache_context, sha: sha) if cache_context
  end
        case mode
        when 'cache-current'
          %w[cache_current_support.rb cache-contract-builder.rb current-cache-validation.rb].each do |file|
            bind_file.call(TASK + '/' + file)
          end
          require_relative 'cache_current_support'
          cache_context = AtlasCurrentCacheSupport.prepare!(task: TASK, stage: OUT,
            sources: sources, lease: lease, record: record, env: env,
            bind: bind_file, read_json: read_bound_json)
          command = cache_context.fetch(:command)
          env = cache_context.fetch(:environment)
        when 'cache-hashes'
          original = ROOT + '/claude/release-v1.2-20261026/metadata-20261026/CacheHashes.lean'
          bind_file.call(original)
          bind_file.call(TASK + '/cache-preparation/CACHE_HASHES.tsv')
          FileUtils.copy_file(original, OUT + '/CacheHashes.lean')
          command = [LEAN, '-j1', '-M1024', '--run', OUT + '/CacheHashes.lean', TASK + '/cache-preparation/CACHE_HASHES.tsv']
        when 'build', 'root'
          raise 'Expected a canonical Atlas module' unless name.match?(/\AAtlas(?:\.[A-Za-z0-9_]+)*\z/)
          relative = name.tr('.', '/')
          source = CANDIDATE + '/' + relative + '.lean'
          raise 'Missing canonical source' unless File.file?(source)
          output = CANDIDATE + '/.lake/build/lib/lean/' + relative
          raise 'Refuse to overwrite a symlinked compiled object' if File.symlink?(output + '.olean')
          FileUtils.mkdir_p(File.dirname(output))
          record[:source] = relative + '.lean'
          record[:source_sha256] = sha.call(source)
          command = [LEAN, *options, '--root=' + CANDIDATE, '-o', output + '.olean', '-i', output + '.ilean', source]
  when 'audit', 'audit-batch', 'audit-public'
          manifest_path = File.expand_path(name)
          raise 'Manifest outside the preparation task' unless manifest_path.start_with?(TASK + '/')
    if mode == 'audit-batch'
      bind_file.call(TASK + '/audit_batch_support.rb')
      require_relative 'audit_batch_support'
      batch_context = AtlasAuditBatches.load_registered!(task: TASK, root: ROOT,
        candidate: CANDIDATE, registry_path: TASK + '/BATCH_REGISTRY.json',
        batch_path: manifest_path, merged: merged, environment: environment,
        stage: OUT, guard: ->(_phase) { check_immutable.call })
      batch_context.fetch(:bindings).each { |path, digest| bind_file.call(path, digest) }
      manifest = batch_context.fetch(:manifest)
      FileUtils.copy_file(TASK + '/BATCH_REGISTRY.json', OUT + '/BATCH_REGISTRY.json')
      FileUtils.copy_file(TASK + '/audit_batch_support.rb', OUT + '/audit_batch_support.rb')
      record[:batch_registry_sha256] = sha.call(OUT + '/BATCH_REGISTRY.json')
      record[:batch_manifest_sha256] = sha.call(manifest_path)
      record[:audit_batch_helper_sha256] = sha.call(OUT + '/audit_batch_support.rb')
      AtlasAuditBatches.announce_stage!(batch_context)
    elsif mode == 'audit-public'
      bind_file.call(TASK + '/public_audit_support.rb')
      require_relative 'public_audit_support'
      public_context = AtlasPublicAuditRegistration.load_registered!(task: TASK, root: ROOT,
        candidate: CANDIDATE, registry_path: TASK + '/PUBLIC_AUDIT_REGISTRY.json',
        manifest_path: manifest_path, sources: sources, environment: environment,
        guard: -> { check_immutable.call })
      public_context.fetch(:bindings).each { |path, digest| bind_file.call(path, digest) }
      manifest = public_context.fetch(:manifest)
      AtlasPublicAuditRegistration.archive!(context: public_context, stage: OUT).each do |path, digest|
        bind_file.call(path, digest)
      end
      record[:public_registry_sha256] = public_context.fetch(:registry_sha256)
      record[:public_manifest_sha256] = public_context.fetch(:manifest_sha256)
      record[:public_roots_sha256] = public_context.fetch(:roots_sha256)
      record[:public_baseline_roots_sha256] = AtlasPublicAuditRegistration::BASELINE_ROOTS_SHA256
      record[:public_audit_helper_sha256] = sha.call(OUT + '/public_audit_support.rb')
      record[:public_collector_inputs_sha256] = sha.call(OUT + '/PUBLIC_COLLECTOR_INPUTS.json')
      record[:public_selection_context_sha256] = sha.call(OUT + '/PUBLIC_SELECTION_CONTEXT.json')
      record[:scope_origin] = 'registered-whole-public-selection'
      record[:whole_public_root_audit] = true
    else
          manifest = read_bound_json.call(manifest_path)
          relative_manifest = manifest_path.delete_prefix(CANDIDATE + '/')
          matches = merged.fetch('scopes').select { |s| s.fetch('manifest') == relative_manifest }
          raise 'A unique registered canonical successor is required' unless matches.size == 1
          historical = matches.first
          raise 'Canonical audit manifest changed' unless sha.call(manifest_path) == historical.fetch('sha256')
          original_path = ROOT + '/' + historical.fetch('original_manifest')
          raise 'Original scope changed' unless sha.call(original_path) == historical.fetch('original_manifest_sha256')
          original_policy = read_bound_json.call(original_path, historical.fetch('original_manifest_sha256'))
          original_modules = merged.fetch('sources').values.to_h { |s| [s.fetch('original_module'), s.fetch('module')] }
          normalized = lambda do |t, remap|
            mod = t['module'] || t.fetch('source').delete_prefix('.lake/packages/mathlib/').delete_suffix('.lean').tr('/', '.')
            [t.fetch('declaration'), remap.fetch(mod, mod), t.fetch('kind')]
          end
          expected_targets = original_policy.fetch('targets').map { |t| normalized.call(t, original_modules) }
          raise 'Original target coverage changed' unless expected_targets == manifest.fetch('targets').map { |t| normalized.call(t, {}) }
          record[:registered_scope] = historical
          record[:scope_origin] = historical['original_receipt'] ? 'historical-passed-scope-canonical-successor' : 'new-thin-interface-scope'
    end
          raise 'A full definition/dependency audit is required' unless manifest['mode'] == 'full' && manifest['definitions'] == true
          raise 'Noncanonical import' unless manifest.fetch('imports').all? { |m| m.match?(/\AAtlas(?:\.[A-Za-z0-9_]+)*\z/) }
          if manifest['environment']
            environment_path = File.expand_path(manifest.fetch('environment'), CANDIDATE)
            raise 'Escaping manifest environment' unless environment_path.start_with?(CANDIDATE + '/')
            declared_environment = read_bound_json.call(environment_path)
            raise 'Manifest environment does not bind the candidate' unless declared_environment == environment
          end
          FileUtils.copy_file(manifest_path, OUT + '/MANIFEST.json')
          root_objects = manifest.fetch('imports').to_h do |m|
            p = CANDIDATE + '/.lake/build/lib/lean/' + m.tr('.', '/') + '.olean'
            raise "Missing compiled canonical import #{m}" unless File.file?(p)
            [p.delete_prefix(CANDIDATE + '/'), sha.call(p)]
          end
          record[:root_objects] = root_objects
          template = File.read(ROOT + '/verification/tools/Extract.lean.in')
          bind_file.call(ROOT + '/verification/tools/Extract.lean.in', Digest::SHA256.hexdigest(template))
          substitutions = {'@@IMPORTS@@' => manifest.fetch('imports').map { |m| 'import ' + m }.join("\n"),
            '@@TARGETS@@' => '#[' + manifest.fetch('targets').map { |t| '(' + t.values_at('declaration', 'module', 'kind').map(&:to_json).join(', ') + ')' }.join(', ') + ']',
            '@@OUTPUT@@' => OUT.to_json, '@@FULL@@' => 'true', '@@DEFINITIONS@@' => 'true'}
          substitutions.each { |a, b| template = template.gsub(a) { b } }
          File.write(OUT + '/Extract.lean', template)
          record[:extractor_sha256] = sha.call(OUT + '/Extract.lean')
          record[:policy_sha256] = sha.call(ROOT + '/verification/tools/policy.rb')
          command = [LEAN, *options, '--root=' + TASK, OUT + '/Extract.lean']
        end
        File.write(OUT + '/INPUTS.json', JSON.pretty_generate(record) + "\n")
        unless %w[cache-hashes cache-current].include?(mode)
          object_index_path = TASK + '/OBJECT_BINDINGS.json'
          object_index_bytes = File.binread(object_index_path)
          object_index = JSON.parse(object_index_bytes)
          bind_file.call(object_index_path, Digest::SHA256.hexdigest(object_index_bytes))
          baseline_cache = nil
          load_baseline_cache = lambda do
            unless baseline_cache
              inventory_path = TASK + '/cache-preparation/CACHE_ARTIFACTS.json'
              cache_result_path = TASK + '/cache-preparation/RESULT.json'
              inventory = read_bound_json.call(inventory_path)
              cache_result = read_bound_json.call(cache_result_path)
              raise 'Baseline cache has no successful validation' unless
                cache_result.fetch('status') == 'baseline-cache-copied-and-trace-hash-verified' &&
                cache_result.fetch('candidate_cache_has_independent_copies') == true &&
                cache_result.fetch('baseline_modules') == inventory.size
              validation = cache_result.fetch('trace_hash_verification')
              raise 'Baseline hash-check reference did not pass' unless validation.fetch('status') == 'passed-baseline-trace-hash-check'
              validation_path = File.expand_path(validation.fetch('receipt'), ROOT)
              raise 'Baseline hash-check receipt escaped task' unless validation_path.start_with?(TASK + '/verification-runs/')
              validated = read_bound_json.call(validation_path)
              raise 'Baseline hash-check receipt did not pass' unless
                validated.fetch('status') == 'passed-baseline-trace-hash-check' &&
                validated.fetch('mode') == 'cache-hashes' && validated.fetch('candidate') == CANDIDATE &&
                validated.fetch('sources_unchanged') == true
              validation_dir = File.dirname(validation_path)
              validation_process = read_bound_json.call(validation_dir + '/' + validated.fetch('process_receipt'),
                validated.fetch('process_receipt_sha256'))
              raise 'Baseline hash-check process did not pass cleanly' unless
                validation_process.fetch('status') == 'process-passed' && validation_process.fetch('exit_code') == 0 &&
                validation_process['signal'].nil? && validation_process['guard_stop'].nil? &&
                validation_process.fetch('proof_diagnostic_errors') == false &&
                validation_process.fetch('command').last == TASK + '/cache-preparation/CACHE_HASHES.tsv'
              bind_file.call(TASK + '/cache-preparation/CACHE_HASHES.tsv')
              validated_sources = read_bound_json.call(validation_dir + '/SOURCE_HASHES.json', validated.fetch('source_hashes_sha256'))
              entries = {}
              inventory.each do |entry|
                key = entry.fetch('source')
                raise "Duplicate baseline cache entry #{key}" if entries.key?(key)
                entries[key] = entry
              end
              baseline_cache = {entries: entries, sources: validated_sources, inventory_path: inventory_path}
              record[:baseline_cache_evidence] = [inventory_path, cache_result_path, validation_path].to_h do |path|
                [path.delete_prefix(TASK + '/'), bound_files.fetch(path)]
              end
            end
            baseline_cache
          end
    import_names = %w[audit audit-batch audit-public].include?(mode) ? manifest.fetch('imports') :
            File.readlines(source).filter_map { |l| l[/^\s*import\s+(.+)$/, 1] }.flat_map { |l| l.split.take_while { |v| !v.start_with?('--') } }
          used_imports = {}
          work = import_names.grep(/\AAtlas(?:\.|\z)/)
          until work.empty?
            mod = work.pop
            next if used_imports.key?(mod)
            binding = object_index.fetch(mod) { raise "Missing source-to-object proof binding for #{mod}" }
            import_source = binding.fetch('source')
            raise "Wrong canonical binding identity #{mod}" unless import_source == mod.tr('.', '/') + '.lean' &&
              binding.fetch('object') == '.lake/build/lib/lean/' + mod.tr('.', '/') + '.olean'
            raise "Stale compiled source for #{mod}" unless sources.fetch(import_source) == binding.fetch('source_sha256')
            raise "Changed compiled input #{mod}" unless sha.call(CANDIDATE + '/' + binding.fetch('object')) == binding.fetch('object_sha256')
            if binding.fetch('basis') == 'fresh-canonical-proof-check'
              previous_path = TASK + '/' + binding.fetch('evidence')
              previous = read_bound_json.call(previous_path)
              raise "Unsuccessful compiled-input receipt #{mod}" unless previous['status'] == 'passed-fresh-canonical-proof-check'
              raise "Compiled-input receipt differs #{mod}" unless previous['name'] == mod &&
                previous['candidate'] == CANDIDATE && previous['source'] == import_source &&
                previous['compiled_object'] == binding.fetch('object') &&
                previous['source_sha256'] == binding.fetch('source_sha256') && previous['compiled_sha256'] == binding.fetch('object_sha256')
              previous_import_hash = previous.fetch('imported_objects_sha256') do
                raise "Prior import snapshot missing for #{mod}; recheck this module"
              end
              previous_imports = read_bound_json.call(File.dirname(previous_path) + '/IMPORTED_OBJECTS.json', previous_import_hash)
              # Compare each saved edge once; do not recursively reopen its receipts here.
              previous_imports.each do |dependency, saved|
                current = object_index.fetch(dependency) { raise "Unbound prior dependency #{dependency} for #{mod}" }
                raise "Prior dependency changed for #{mod}: #{dependency}; recheck this module" unless
                  binding_identity.call(saved) == binding_identity.call(current)
              end
            elsif binding.fetch('basis') == 'validated-published-baseline-cache'
              cache = load_baseline_cache.call
              raise "Wrong baseline evidence reference #{mod}" unless
                File.expand_path(binding.fetch('evidence'), TASK) == cache.fetch(:inventory_path)
              cached = cache.fetch(:entries).fetch(import_source) { raise "Missing validated baseline entry #{mod}" }
              raise "Baseline source binding differs #{mod}" unless
                baseline_sources.fetch(import_source) == binding.fetch('source_sha256') &&
                cache.fetch(:sources).fetch(import_source) == binding.fetch('source_sha256') &&
                cached.fetch('candidate_source_sha256') == binding.fetch('source_sha256')
              raise "Baseline object binding differs #{mod}" unless
                cached.fetch('compiled_object') == CANDIDATE + '/' + binding.fetch('object') &&
                cached.fetch('compiled_sha256') == binding.fetch('object_sha256')
            else
              raise "Unsupported compiled-input provenance #{mod}"
            end
            used_imports[mod] = binding
            File.foreach(CANDIDATE + '/' + import_source) do |line|
              next unless (tail = line[/^\s*import\s+(.+)$/, 1])
              direct = tail.split.take_while { |v| !v.start_with?('--') }.grep(/\AAtlas(?:\.|\z)/)
              if binding.fetch('basis') == 'fresh-canonical-proof-check'
                raise "Incomplete prior import snapshot for #{mod}; recheck this module" unless (direct - previous_imports.keys).empty?
              end
              work.concat(direct)
            end
          end
          File.write(OUT + '/IMPORTED_OBJECTS.json', JSON.pretty_generate(used_imports.sort.to_h) + "\n")
          record[:imported_objects_sha256] = sha.call(OUT + '/IMPORTED_OBJECTS.json')
          record[:source_to_object_bindings_verified] = true
        end
        FileUtils.copy_file(__FILE__, OUT + '/verification-driver.rb')
        FileUtils.copy_file(TASK + '/monitor.rb', OUT + '/process-monitor.rb')
        File.write(OUT + '/INPUTS.json', JSON.pretty_generate(record) + "\n")
        if mode == 'cache-current'
          bind_file.call(OUT + '/verification-driver.rb', record.fetch(:tool_sha256))
          bind_file.call(OUT + '/process-monitor.rb', record.fetch(:monitor_sha256))
          bind_file.call(OUT + '/ENVIRONMENT.json', record.fetch(:environment_sha256))
          bind_file.call(OUT + '/MERGED_SOURCES.json', record.fetch(:integration_registry_sha256))
          bind_file.call(OUT + '/INPUTS.json')
        end
        puts "#{mode}: #{name}; #{OUT}"
        $stdout.flush
        process = ReleasePreparationMonitor.run(OUT, 'process', command, env: env, cwd: CANDIDATE,
          held_lease: lease, inherit_held_lease: mode == 'cache-current')
        record[:process_receipt] = 'process.json'
        record[:process_receipt_sha256] = sha.call(OUT + '/process.json')
        raise "Process #{process[:status]}: #{process[:failure] || process[:guard_stop] || process[:diagnostic_examples]}" unless process[:status] == 'process-passed'
        check_immutable.call
        case mode
        when 'cache-current'
          AtlasCurrentCacheSupport.finalize!(context: cache_context, sources: sources,
            record: record, process: process, bind: bind_file, read_json: read_bound_json, sha: sha)
          pending_status = 'passed-current-cache-integrity'
        when 'build', 'root'
          record[:compiled_object] = output.delete_prefix(CANDIDATE + '/') + '.olean'
          record[:compiled_sha256] = sha.call(output + '.olean')
          pending_status = 'passed-fresh-canonical-proof-check'
          new_object_binding = {'source' => record.fetch(:source), 'source_sha256' => record.fetch(:source_sha256),
            'object' => record.fetch(:compiled_object), 'object_sha256' => record.fetch(:compiled_sha256),
            'basis' => 'fresh-canonical-proof-check', 'evidence' => (OUT + '/RESULT.json').delete_prefix(TASK + '/')}
        when 'cache-hashes'
          pending_status = 'passed-baseline-trace-hash-check'
  when 'audit', 'audit-batch', 'audit-public'
          # Socrates public-review: bind the bytes BEFORE the first parse/policy
          # evaluation, including the raw graph. Final immutability rehashes them.
          bind_file.call(OUT + '/declarations.jsonl')
          bind_file.call(OUT + '/dependencies.jsonl')
          declarations = File.readlines(OUT + '/declarations.jsonl').map { |line| JSON.parse(line) }
          expected = manifest.fetch('targets').map { |t| t.fetch('declaration') }
          raise 'Incomplete or mismatched declaration extraction' unless declarations.map { |d| d.fetch('declaration') } == expected
          graph = {}
          File.foreach(OUT + '/dependencies.jsonl') do |line|
            node = JSON.parse(line)
            raise 'Duplicate graph node' if graph.key?(node.fetch('name'))
            graph[node.fetch('name')] = node
          end
          record[:boundaries] = AtlasVerification.check_policy(manifest, declarations, graph)
    if mode == 'audit-batch'
      after_sources = source_map.call
      raise 'Sources changed before scoped audits' unless after_sources == sources
      File.write(OUT + '/SOURCE_HASHES_AFTER.json', JSON.pretty_generate(after_sources) + "\n")
      bind_file.call(OUT + '/SOURCE_HASHES_AFTER.json')
      batch_outcome = AtlasAuditBatches.finalize!(context: batch_context, graph: graph,
        declarations: declarations, manifest: manifest, merged: merged, stage: OUT,
        process_path: OUT + '/process.json', log_path: OUT + '/process.log.gz')
      batch_outcome.fetch(:bound_files).each { |path, digest| bind_file.call(path, digest) }
      record[:batch_evidence_sha256] = batch_outcome.fetch(:evidence_sha256)
      record[:batch_scopes] = batch_outcome.fetch(:scopes)
    elsif mode == 'audit-public'
      AtlasPublicAuditRegistration.declarations_match!(public_context, declarations)
      after_sources = source_map.call
      raise 'Sources changed during whole-public audit' unless after_sources == sources
      File.write(OUT + '/SOURCE_HASHES_AFTER.json', JSON.pretty_generate(after_sources) + "\n")
      bind_file.call(OUT + '/SOURCE_HASHES_AFTER.json')
    end
          if historical && historical['original_receipt']
            origins = merged.fetch('sources').values.to_h { |s| [s.fetch('module'), s.fetch('original_module')] }
            transported = graph.transform_values { |n| n.merge('module' => origins.fetch(n.fetch('module'), n.fetch('module'))) }
            record[:historical_policy_boundaries_on_current_graph] = AtlasVerification.check_policy(original_policy, declarations, transported)
            record[:historical_policy_sha256] = historical.fetch('original_manifest_sha256')
            record[:historical_policy_transport] = 'Canonical defining modules mapped back to their byte-bound original source identities; the original policy is checked on the complete newly extracted graph. This is new evidence, not a relabelled historical run.'
          end
          record[:targets] = expected.size
          record[:dependency_nodes] = graph.size
          record[:allowed_axioms] = manifest.fetch('allowed_axioms')
          record[:axioms] = declarations.flat_map { |d| d.fetch('axioms') }.uniq.sort
          record[:full_dependency_audit] = true
          used = graph.values.map { |n| n.fetch('module') }.uniq.grep(/\AAtlas(?:\.|\z)/)
          used_sources = used.to_h do |m|
            p = m.tr('.', '/') + '.lean'
            [p, sources.fetch(p)]
          end
          File.write(OUT + '/PROJECT_SOURCES.json', JSON.pretty_generate(used_sources.sort.to_h) + "\n")
          artifacts = used.to_h do |m|
            p = '.lake/build/lib/lean/' + m.tr('.', '/') + '.olean'
            [p, sha.call(CANDIDATE + '/' + p)]
          end
          File.write(OUT + '/PROJECT_COMPILED_ARTIFACTS.json', JSON.pretty_generate(artifacts.sort.to_h) + "\n")
          raise 'Compiled import changed during audit' unless root_objects.all? { |p, h| sha.call(CANDIDATE + '/' + p) == h }
    pending_status = mode == 'audit-batch' ? 'passed-full-canonical-batch-audit' : 'passed-full-canonical-dependency-audit'
        end
        record[:status] = 'finalizing'
        # Compression remains guarded work, so a stop is caught before minimal cleanup.
        if File.file?(OUT + '/dependencies.jsonl')
          Zlib::GzipWriter.open(OUT + '/dependencies.jsonl.gz', Zlib::BEST_SPEED) do |z|
            z.mtime = 0
            File.open(OUT + '/dependencies.jsonl', 'rb') { |f| IO.copy_stream(f, z) }
          end
          record[:dependency_log_sha256] = sha.call(OUT + '/dependencies.jsonl')
          record[:dependency_log_compressed_sha256] = sha.call(OUT + '/dependencies.jsonl.gz')
          if %w[audit audit-batch audit-public].include?(mode)
            bind_file.call(OUT + '/dependencies.jsonl.gz', record.fetch(:dependency_log_compressed_sha256))
          end
        end
        if mode == 'audit-public'
          # Keep every public result input/output bound through the same final
          # immutability check, watchdog and held lease; no new success path.
          %w[MANIFEST.json declarations.jsonl dependencies.jsonl.gz
            SOURCE_HASHES_AFTER.json IMPORTED_OBJECTS.json PROJECT_SOURCES.json
            PROJECT_COMPILED_ARTIFACTS.json process.json process.log.gz].each do |artifact|
            bind_file.call(OUT + '/' + artifact)
          end
        end
        File.write(OUT + '/BOUND_INPUTS.json', JSON.pretty_generate(bound_files.sort.to_h) + "\n")
        record[:bound_inputs_sha256] = bind_file.call(OUT + '/BOUND_INPUTS.json')
        check_immutable.call
        record[:sources_unchanged] = true
        record[:final_immutability_verified] = true
        ready_to_commit = true
      end
    rescue StandardError => e
      mark_failure.call(e)
    ensure
      begin
        watchdog&.kill
        watchdog&.join
        if record[:ruby_guard_stop] || Thread.current.pending_interrupt?(PreparationMemoryStop)
          mark_failure.call(PreparationMemoryStop.new('Memory/worker stop before receipt commit'))
        elsif !ready_to_commit && !%w[memory-stopped not-passed].include?(record[:status])
          mark_failure.call(StandardError.new('Stage interrupted before final immutability check'))
        end
        record[:finished_utc] = Time.now.utc.iso8601
        if ready_to_commit
          AtlasCurrentCacheSupport.final_guard!(cache_context, record: record) if mode == 'cache-current'
          record[:status] = pending_status
          receipt_next = OUT + '/RESULT.next.json'
          File.open(receipt_next, File::WRONLY | File::CREAT | File::EXCL, 0o644) do |file|
            file.write(JSON.pretty_generate(record) + "\n")
          end
          File.rename(receipt_next, OUT + '/RESULT.json')
          # Never publish an object binding until its passing receipt exists.
          if new_object_binding
            object_index[name] = new_object_binding
            next_index = TASK + '/OBJECT_BINDINGS.next-' + Process.pid.to_s + '.json'
            File.open(next_index, File::WRONLY | File::CREAT | File::EXCL, 0o644) do |file|
              file.write(JSON.pretty_generate(object_index) + "\n")
            end
            File.rename(next_index, object_index_path)
          end
        else
          write_minimal_failure.call
        end
      rescue StandardError => e
        mark_failure.call(e)
        write_minimal_failure.call
      ensure
        begin
          lease&.flock(File::LOCK_UN)
        ensure
          lease&.close
        end
      end
    end
  end
rescue PreparationMemoryStop
  # A deferred stop is delivered only after the failure receipt and cleanup above.
end
puts JSON.pretty_generate(record.slice(:status, :targets, :dependency_nodes, :failure))
exit(record[:status].start_with?('passed-') ? 0 : 1)
