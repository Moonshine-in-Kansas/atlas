# Source-only parent integration, loaded only for mode cache-current.
# No Lean/Lake invocation, policy evaluation or second lease is introduced.
require_relative 'cache-contract-builder'
require 'fileutils'
require 'open3'

module AtlasCurrentCacheSupport
  ROOT = AtlasCurrentCacheContract::ROOT
  COUNTS = {'baseline_objects' => 4865, 'new_normal_proofs' => 266,
    'fresh_root_elaborations' => 2, 'objects' => 5133, 'source_and_pin_entries' => 5136}.freeze
  FALSE_FLAGS = %w[fresh_whole_project_rebuild fresh_project_rebuild independent_replay
    new_proof_build new_full_dependency_audit new_lake_hash_evaluation_performed].freeze
  PAYLOADS = %w[SOURCE_HASHES.json SOURCE_HASHES_AFTER.json CACHE_SOURCE_HASHES.json
    CACHE_ARTIFACTS.json CACHE_ARTIFACTS_AFTER.json OBJECT_BINDINGS.json
    ORIGINAL_CACHE_SOURCE_HASHES.json ORIGINAL_CACHE_ENVIRONMENT.json COMPILED_SOURCE_HASHES.json
    SOURCE_COMPATIBILITY.json OBJECT_ORIGINS.json IMPORTED_OBJECT_EDGES.json
    PACKAGES_BEFORE.json PACKAGES_AFTER.json PROVENANCE.json INPUT_BINDINGS.json].freeze
  def self.need(condition, message)
    raise message unless condition
  end
  def self.member(base, relative)
    need(relative.is_a?(String) && !relative.empty? && !relative.start_with?('/') &&
      relative.split('/').none? { |part| part.empty? || %w[. ..].include?(part) }, 'Nonportable cache payload member')
    path = base + '/' + relative
    need(File.realpath(path) == path && File.file?(path), 'Cache payload is not an ordinary file')
    path
  end
  def self.prepare!(task:, stage:, sources:, lease:, record:, env:, bind:, read_json:)
    %w[cache_current_support.rb cache-contract-builder.rb current-cache-validation.rb].each do |file|
      hash = bind.call(task + '/' + file)
      FileUtils.copy_file(task + '/' + file, stage + '/' + file)
      bind.call(stage + '/' + file, hash)
    end
    context = AtlasCurrentCacheContract.build!(task: task, stage: stage, sources: sources,
      lease: lease, driver_sha: record.fetch(:tool_sha256), monitor_sha: record.fetch(:monitor_sha256),
      bind: bind, read_json: read_json)
    context.merge!(task: task, stage: stage, sources: sources, lease: lease, finalized: false,
      contract_guard: context.fetch(:contract).fetch('parent_guard'))
    context[:environment] = env.merge('ATLAS_CACHE_CONTRACT_SHA256' => context.fetch(:sha256),
      'ATLAS_CACHE_LEASE_FD' => lease.fileno.to_s)
    context[:command] = [RbConfig.ruby, task + '/current-cache-validation.rb',
      '--contract', context.fetch(:path), '--out', context.fetch(:output)]
    record[:cache_contract] = 'CACHE_CONTRACT.json'
    record[:cache_contract_sha256] = context.fetch(:sha256)
    record[:cache_validator_sha256] = context.fetch(:validator_sha256)
    record[:cache_support_sha256] = bind.call(stage + '/cache_current_support.rb')
    record[:cache_contract_builder_sha256] = bind.call(stage + '/cache-contract-builder.rb')
    context
  end
  def self.packages!(context)
    # Read-only Git only, no fetch/download/checkout/config mutation or new lease.
    expected = context.fetch(:packages)
    env = {'GIT_OPTIONAL_LOCKS' => '0', 'GIT_TERMINAL_PROMPT' => '0',
      'GIT_NO_LAZY_FETCH' => '1', 'GIT_LFS_SKIP_SMUDGE' => '1'}
    expected.each do |path, entry|
      need(path.match?(%r{\A\.lake/packages/[A-Za-z0-9_-]+\z}), 'Invalid package member')
      dir = File.realpath(ROOT + '/' + path)
      need(dir == entry.fetch('resolved_path') && entry.fetch('working_tree_clean') == true &&
        entry.fetch('untracked_nonignored_clean') == true, 'Package path/cleanliness binding changed')
      git = ['git', '--no-optional-locks', '-c', 'core.fsmonitor=false',
        '-c', 'core.untrackedCache=false', '-C', dir]
      head, error, status = Open3.capture3(env, *git, 'rev-parse', '--verify', 'HEAD')
      need(status.success? && head.strip == entry.fetch('revision'), "Package revision drift #{path}: #{error}")
      dirty, error, status = Open3.capture3(env, *git, 'status', '--porcelain=v1',
        '--untracked-files=all', '--ignore-submodules=none')
      need(status.success? && dirty.empty?, "Package became dirty #{path}: #{error}")
    end
  end
  def self.immutable!(context, sha:)
    return unless context && context[:finalized]
    need(AtlasCurrentCacheContract.observe_host!.fetch('anchor') ==
      context.fetch(:contract_guard).fetch('host_visibility_anchor'), 'Live reviewed host anchor changed before finalization')
    root = context.fetch(:task) + '/candidate'
    context.fetch(:sources).each_key do |relative|
      path = root + '/' + relative
      need(File.realpath(path) == path && File.file?(path), 'Current source/pin became nonordinary')
    end
    current = (Dir.glob(root + '/.lake/build/lib/lean/Atlas/**/*.olean') +
      [root + '/.lake/build/lib/lean/Atlas.olean']).sort.to_h do |path|
      need(File.realpath(path) == path && File.file?(path) && File.stat(path).nlink == 1,
        'Cache object became linked/nonordinary')
      [path.delete_prefix(root + '/'), sha.call(path)]
    end
    need(current == context.fetch(:artifacts), 'Actual current cache changed before parent finalization')
    packages!(context)
  end
  def self.finalize!(context:, sources:, record:, process:, bind:, read_json:, sha:)
    stage = context.fetch(:stage)
    out = context.fetch(:output)
    need(process.fetch(:status) == 'process-passed' && process.fetch(:exit_code) == 0 &&
      process.fetch(:signal).nil? && process.fetch(:guard_stop).nil? && process[:failure].nil? &&
      process.fetch(:proof_diagnostic_errors) == false && process.fetch(:log_recovery_verified) == true &&
      process.fetch(:command) == context.fetch(:command) && process.fetch(:environment) == context.fetch(:environment),
      'Actual cache child process did not pass under the parent monitor')
    lease = context.fetch(:lease)
    need(process.fetch(:inherited_held_lease) == {descriptor: lease.fileno, device: lease.stat.dev,
      inode: lease.stat.ino, owner_pid: Process.pid, parent_owned: true}, 'Wrong actual monitor lease inheritance')
    path = member(out, 'CACHE_BINDING.json')
    binding_sha = bind.call(path)
    binding = read_json.call(path, binding_sha)
    need(binding.fetch('format') == 1 && binding.fetch('status') == 'validated-current-cache-integrity-child-result' &&
      binding.fetch('counts') == COUNTS && binding.fetch('parent_contract_sha256') == context.fetch(:sha256) &&
      binding.fetch('tool_sha256') == context.fetch(:validator_sha256) &&
      binding.fetch('parent_monitor_finalization_required') == true &&
      binding.fetch('current_cache_integrity_validation_performed') == true &&
      binding.fetch('original_receipts_unchanged') == true && binding.fetch('sources_unchanged') == true &&
      binding.fetch('cache_artifacts_unchanged') == true, 'Wrong child cache binding or scope')
    FALSE_FLAGS.each { |field| need(binding.fetch(field) == false, 'Cache evidence cannot be promoted to proof replay') }
    child_lease = binding.fetch('inherited_held_lease')
    guard = context.fetch(:contract_guard)
    need(child_lease.fetch('host_visibility_anchor') == guard.fetch('host_visibility_anchor') &&
      child_lease.fetch('host_observer') == {'pid' => process.fetch(:pid), 'uid' => 1000,
        'nspid' => [process.fetch(:pid)], 'pid_namespace' => guard.fetch('host_pid_namespace')},
      'Child did not observe the reviewed live host chain and its own namespace depth')
    need(child_lease.values_at('supervisor_pid', 'supervisor_starttime', 'host_pid_namespace', 'inherited_fd', 'lease_device', 'lease_inode') ==
      [Process.pid, guard.fetch('supervisor_starttime'), guard.fetch('host_pid_namespace'), lease.fileno, lease.stat.dev, lease.stat.ino],
      'Child did not observe the actual parent held lease/host namespace')
    files = binding.fetch('files')
    need((PAYLOADS - files.keys).empty?, 'Missing actual cache payloads')
    files.each do |relative, hash|
      need(hash.is_a?(String) && hash.match?(/\A[0-9a-f]{64}\z/), 'Invalid child payload hash')
      bind.call(member(out, relative), hash)
    end
    actual_files = Dir.glob(out + '/**/*').select { |file| File.file?(file) }.map { |file| file.delete_prefix(out + '/') }.sort
    need(actual_files == (files.keys + ['CACHE_BINDING.json']).sort, 'Extra or missing child payload file')
    document = ->(name) { read_json.call(member(out, name), files.fetch(name)) }
    %w[SOURCE_HASHES.json SOURCE_HASHES_AFTER.json CACHE_SOURCE_HASHES.json].each do |name|
      need(document.call(name) == sources, 'Current full source/pin snapshot is not exact')
    end
    artifacts = document.call('CACHE_ARTIFACTS.json')
    need(artifacts == document.call('CACHE_ARTIFACTS_AFTER.json') && artifacts.size == 5133,
      'Cache before/after map differs')
    index = document.call('OBJECT_BINDINGS.json')
    need(index == read_json.call(context.fetch(:task) + '/OBJECT_BINDINGS.json') && index.size == 5133,
      'Final current object index differs')
    expected_artifacts = index.to_h do |mod, entry|
      need(entry.fetch('source') == mod.tr('.', '/') + '.lean' &&
        entry.fetch('source_sha256') == sources.fetch(entry.fetch('source')) &&
        entry.fetch('object') == '.lake/build/lib/lean/' + mod.tr('.', '/') + '.olean', 'Wrong current object/source identity')
      [entry.fetch('object'), entry.fetch('object_sha256')]
    end
    need(expected_artifacts == artifacts, 'Object index and actual artifact hashes differ')
    packages = document.call('PACKAGES_BEFORE.json')
    need(packages == document.call('PACKAGES_AFTER.json'), 'Package before/after differs')
    environment = read_json.call(context.fetch(:task) + '/CANDIDATE_ENVIRONMENT.json')
    need(packages.transform_values { |entry| entry.fetch('revision') } == environment.fetch('revisions'),
      'Package checks do not cover every public dependency revision')
    document.call('INPUT_BINDINGS.json').each do |input, hash|
      need(input.start_with?(ROOT + '/') && File.realpath(input) == input && File.file?(input),
        'Child provenance path escaped the ordinary checkout')
      bind.call(input, hash)
    end
    # This is the child's actual after snapshot, copied verbatim, not fabricated
    # from the before snapshot or retroactively added to an old RESULT.
    FileUtils.copy_file(member(out, 'SOURCE_HASHES_AFTER.json'), stage + '/SOURCE_HASHES_AFTER.json')
    record[:source_hashes_after_sha256] = bind.call(stage + '/SOURCE_HASHES_AFTER.json', files.fetch('SOURCE_HASHES_AFTER.json'))
    bind.call(stage + '/process.json', record.fetch(:process_receipt_sha256))
    bind.call(stage + '/process.log.gz', process.fetch(:log_compressed_sha256))
    context.merge!(finalized: true, artifacts: artifacts, packages: packages)
    immutable!(context, sha: sha)
    record.merge!(cache_binding: 'cache/CACHE_BINDING.json', cache_binding_sha256: binding_sha,
      cache_artifacts: 'cache/CACHE_ARTIFACTS.json', cache_artifacts_sha256: files.fetch('CACHE_ARTIFACTS.json'),
      cache_artifacts_after: 'cache/CACHE_ARTIFACTS_AFTER.json', cache_artifacts_after_sha256: files.fetch('CACHE_ARTIFACTS_AFTER.json'),
      object_bindings: 'cache/OBJECT_BINDINGS.json', object_bindings_sha256: files.fetch('OBJECT_BINDINGS.json'),
      current_object_index_sha256: context.fetch(:contract).fetch('anchors').fetch('OBJECT_BINDINGS').fetch('sha256'),
      cache_counts: COUNTS, cache_artifacts_unchanged: true, original_receipts_unchanged: true,
      source_to_object_bindings_verified: true, current_cache_integrity_validation_performed: true,
      scope_origin: 'actual-current-cache-integrity-with-original-proof-provenance',
      source_binding_semantics: binding.fetch('source_binding_semantics'))
    FALSE_FLAGS.each { |field| record[field.to_sym] = false }
  end
  def self.final_guard!(context, record:)
    # Called after the orchestration watchdog has joined and immediately before
    # atomic outer RESULT publication, while the same parent lease remains held.
    visibility = AtlasCurrentCacheContract.observe_host!
    need(visibility.fetch('anchor') == context.fetch(:contract_guard).fetch('host_visibility_anchor'),
      'Reviewed host anchor changed before the outer RESULT commit')
    memory = ReleasePreparationMonitor.memory
    workers = ReleasePreparationMonitor.workers
    rss = File.read('/proc/self/status')[/^VmRSS:\s+(\d+)/, 1].to_i * 1024
    unless memory.fetch('MemAvailable') >= 1024**3 && rss < 9 * 1024**3 &&
        workers.fetch(:combined_rss) < memory.fetch('MemTotal') * 2 / 3 && workers.fetch(:total_lean) <= 4
      record[:ruby_guard_stop] = {memory: memory, workers: workers, supervisor_rss: rss,
        phase: 'cache-current-final-guard'}
      raise PreparationMemoryStop, 'Actual host final memory/worker guard failed'
    end
    lease = context.fetch(:lease)
    need(!lease.closed? && AtlasCurrentCacheContract.starttime(Process.pid) ==
      context.fetch(:contract_guard).fetch('supervisor_starttime'), 'Parent lease/identity lost before outer commit')
    lock = ROOT + '/verification/chevalley/.runner.lock'
    need(!File.symlink?(lock) && [lease.stat.dev, lease.stat.ino] == [File.stat(lock).dev, File.stat(lock).ino] &&
      File.readlink('/proc/self/ns/pid') == context.fetch(:contract_guard).fetch('host_pid_namespace'),
      'Lease pathname or host namespace changed before outer commit')
    owner_lock = File.read("/proc/self/fdinfo/#{lease.fileno}").lines.find do |line|
      line.match?(/\Alock:\s+\d+: FLOCK\s+ADVISORY\s+WRITE\s+#{Process.pid}\s+/) &&
        line.split[-3].split(':').last.to_i == lease.stat.ino && line.split.last(2) == %w[0 EOF]
    end
    need(owner_lock, 'Parent exclusive FLOCK is no longer held at outer commit')
    record[:cache_final_guard] = {status: 'passed', memory: memory, workers: workers,
      supervisor_rss: rss, supervisor_pid: Process.pid, held_lease_descriptor: lease.fileno,
      host_pid_namespace: File.readlink('/proc/self/ns/pid'), fdinfo_lock: owner_lock.strip,
      host_visibility_anchor: visibility.fetch('anchor'), host_observer: visibility.fetch('observer')}
  end
end
