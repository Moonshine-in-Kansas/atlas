# Source-only proposal. Loaded by the reviewed parent inside its existing lease
# and watchdog, after 266 normal checks and both root elaborations. No subprocess,
# proof build, evaluator, lock acquisition or candidate write occurs in this file.
require 'json'
require 'digest'
require 'rbconfig'

module AtlasCurrentCacheContract
  ROOT = '/home/gerald/atlas'
  TASK = ROOT + '/claude/release-update-v1.2-20261030'
  PUBLIC_BASE_SHA256 = 'c2ef2d48d100800a107778eead0a67884f4dd8a91516d3b740f4df0c0a74fc3a'
  HISTORICAL_MONITOR = '3f6d0d60c694fa9fb64c678e690e553f5fac6b65a6e82e1838c57157068eac55'
  REVIEWED_DRIVERS = %w[
    68676739e8522114ae0ab9e384facbbf950e4a91628eaec5d04b5839b6a9ebad
    647ae1c69c79a17c9365d98bca2dee007b74fd293a069f2928db86ad32b227a6
  ].freeze
  # These are observed actual artifact hashes, not generated receipts. The old
  # RESULT lacks a TSV SHA; this explicit review anchor does not retrofit one.
  HISTORY = {
    'BASELINE_EXPORT' => ['BASELINE_EXPORT.json', '35ef9e63982986bcda6843a89b41349aceabdf3f581e185fcbde3397f017b59f'],
    'CACHE_ARTIFACTS' => ['cache-preparation/CACHE_ARTIFACTS.json', '838be9fd3285f370649e28d9ae8090cee043e2ae53e54b017942a1e5d41dfe87'],
    'CACHE_PREPARATION_RESULT' => ['cache-preparation/RESULT.json', '8a2d72c53dab33128664524dc7c0ee58a599b37b4f2ed80265599060a6cc4969'],
    'CACHE_HASHES_TSV' => ['cache-preparation/CACHE_HASHES.tsv', '653c1f4a640337cb526be23271d198e84bc146ec749205d3ef41f78c31699590'],
    'BASELINE_HASH_RESULT' => ['verification-runs/20261030T042504-cache-hashes-baseline/RESULT.json', '3e550f54a7be1730a4d2ee2f23cc25b1481a12eba6b28b8fbf157b2872a9be69'],
    'BASELINE_HASH_CHECKER' => ['verification-runs/20261030T042504-cache-hashes-baseline/CacheHashes.lean', 'f4bc3a9c7cc86e794a78fad31afc3f560ddb9735c80df83ff1fdd5f5d9c5d68c'],
    'LICENCE_BINDING' => ['candidate/verification/release-candidate/LICENCE_BINDING.json', 'a76c5cfd93395d9f3f9a72ef51d68a11929a3303be8a2d7755027653d32f5ca3'],
    'HISTORICAL_CACHE_SOURCE_HASHES' => ['candidate/verification/2026-10-26-cache-audit/CACHE_SOURCE_HASHES.json', '52da2fe7ec9238b2a5255c2fd9a2f90b6105ede7a7986a8f7b8a2f7b43f76dc1']
  }.freeze
  def self.need(condition, message)
    raise message unless condition
  end
  def self.starttime(pid)
    File.read("/proc/#{pid}/stat").sub(/\A\d+ \(.*\) /, '').split.fetch(19)
  end
  # Exact chain established by the parent's read-only host inspection. No PID
  # discovery by name and no fallback when one of these identities disappears.
  # PID1 and user-systemd namespace links are inaccessible to this uid; neither
  # is read or represented as an observed namespace by this implementation.
  HOST_NAMESPACE = 'pid:[4026531836]'
  HOST_CHAIN = [
    {'pid' => 1450, 'comm' => 'plasmashell', 'uid' => 1000, 'ppid' => 1140, 'starttime' => '1269', 'nspid' => [1450]},
    {'pid' => 1140, 'comm' => 'systemd', 'uid' => 1000, 'ppid' => 1, 'starttime' => '804', 'nspid' => [1140]},
    {'pid' => 1, 'comm' => 'systemd', 'uid' => 0, 'ppid' => 0, 'starttime' => '9', 'nspid' => [1]}
  ].freeze
  def self.status_numbers(status, field)
    text = status[/^#{Regexp.escape(field)}:\s+([^\n]+)$/, 1]
    need(text && text.split.all? { |value| value.match?(/\A\d+\z/) }, "Missing or malformed proc #{field}")
    text.split.map { |value| Integer(value, 10) }
  end
  def self.host_process!(expected)
    pid = expected.fetch('pid')
    base = "/proc/#{pid}"
    raw = File.read(base + '/stat')
    match = raw.match(/\A(\d+) \((.*)\) /)
    need(match && match[1].to_i == pid && match[2] == expected.fetch('comm'), 'Host anchor stat identity changed')
    fields = raw.sub(/\A\d+ \(.*\) /, '').split
    need(!%w[Z X x].include?(fields.fetch(0)), 'Host anchor is no longer alive')
    status = File.read(base + '/status')
    comm = File.read(base + '/comm').strip
    need(status_numbers(status, 'Pid') == [pid] && status_numbers(status, 'Tgid') == [pid] &&
      status[/^Name:\s+([^\n]+)$/, 1] == comm &&
      status_numbers(status, 'Uid') == [expected.fetch('uid')] * 4 &&
      status_numbers(status, 'PPid') == [Integer(fields.fetch(1), 10)], 'Host anchor proc identity disagrees')
    observed = {'pid' => pid, 'comm' => comm, 'uid' => status_numbers(status, 'Uid').first,
      'ppid' => Integer(fields.fetch(1), 10), 'starttime' => fields.fetch(19),
      'nspid' => status_numbers(status, 'NSpid')}
    need(observed == expected, 'Reviewed host anchor UID/starttime/ancestry/NSpid changed')
    observed
  end
  def self.observe_host!
    before = HOST_CHAIN.map { |expected| host_process!(expected) }
    desktop_namespace = File.readlink('/proc/1450/ns/pid')
    status = File.read('/proc/self/status')
    observer = {'pid' => Process.pid, 'uid' => Process.uid, 'nspid' => status_numbers(status, 'NSpid'),
      'pid_namespace' => File.readlink('/proc/self/ns/pid')}
    need(Process.uid == 1000 && Process.euid == 1000 && status_numbers(status, 'Uid') == [1000] * 4 &&
      status_numbers(status, 'Pid') == [Process.pid] && observer.fetch('nspid') == [Process.pid] &&
      desktop_namespace == HOST_NAMESPACE && observer.fetch('pid_namespace') == desktop_namespace,
      'Observer is not in the reviewed desktop host namespace at depth one')
    # Bracket the namespace observations by complete live-chain identity reads.
    need(HOST_CHAIN.map { |expected| host_process!(expected) } == before, 'Host anchor changed during observation')
    {'anchor' => {'method' => 'parent-reviewed-kde-session-chain-v1', 'chain' => before,
      'namespace_source_pid' => 1450, 'pid_namespace' => desktop_namespace,
      'unreadable_namespace_pids_not_observed' => [1140, 1]}, 'observer' => observer}
  end
  def self.build!(task:, stage:, sources:, lease:, driver_sha:, monitor_sha:, bind:, read_json:)
    need(task == TASK && File.realpath(task) == task, 'Wrong cache-current task')
    need(File.dirname(stage) == task + '/verification-runs' &&
      File.basename(stage).match?(/\A\d{8}T\d{6}-cache-current-current\z/), 'Wrong cache-current stage')
    visibility = observe_host!
    namespace = visibility.fetch('observer').fetch('pid_namespace')
    stat = lease.stat
    lock = ROOT + '/verification/chevalley/.runner.lock'
    need(lease.path == lock && !File.symlink?(lock) &&
      [stat.dev, stat.ino] == [File.stat(lock).dev, File.stat(lock).ino], 'Wrong held parent lease')
    lock_line = File.read("/proc/self/fdinfo/#{lease.fileno}").lines.find do |line|
      line.match?(/\Alock:\s+\d+: FLOCK\s+ADVISORY\s+WRITE\s+#{Process.pid}\s+/) &&
        line.split[-3].split(':').last.to_i == stat.ino && line.split.last(2) == %w[0 EOF]
    end
    need(lock_line, 'The parent must already own the exclusive FLOCK; no new lease is acquired')
    anchors = HISTORY.to_h do |name, (rel, expected)|
      path = task + '/' + rel
      need(File.realpath(path) == path, 'Historical anchor may not be symlinked')
      bind.call(path, expected)
      [name, {'path' => path, 'sha256' => expected}]
    end
    {'OBJECT_BINDINGS' => task + '/OBJECT_BINDINGS.json',
     'MERGED_SOURCES' => task + '/MERGED_SOURCES.json',
     'INTEGRATION_ORDER' => task + '/INTEGRATION_ORDER.json',
     'CANDIDATE_ENVIRONMENT' => task + '/CANDIDATE_ENVIRONMENT.json',
     'CURRENT_SOURCE_HASHES' => stage + '/SOURCE_HASHES.json'}.each do |name, path|
      need(File.realpath(path) == path, 'Current anchor may not be symlinked')
      anchors[name] = {'path' => path, 'sha256' => bind.call(path)}
    end
    index = read_json.call(task + '/OBJECT_BINDINGS.json')
    merged = read_json.call(task + '/MERGED_SOURCES.json')
    need(index.size == 5133 && merged.fetch('sources').size == 266 && sources.size == 5136,
      'Wait for all 4865 baseline + 266 new + 2 root bindings')
    modules = merged.fetch('sources').values.map { |row| row.fetch('module') }
    reviewed_pairs = (REVIEWED_DRIVERS.map { |hash| [hash, HISTORICAL_MONITOR] } + [[driver_sha, monitor_sha]]).uniq
    (modules + %w[Atlas Atlas.Audit]).each do |mod|
      binding = index.fetch(mod)
      evidence = binding.fetch('evidence')
      need(evidence.match?(%r{\Averification-runs/[^/]+/RESULT\.json\z}), 'Wrong genuine proof receipt path')
      receipt = read_json.call(task + '/' + evidence)
      root = %w[Atlas Atlas.Audit].include?(mod)
      need(binding.fetch('basis') == 'fresh-canonical-proof-check' &&
        receipt.fetch('status') == 'passed-fresh-canonical-proof-check' &&
        receipt.fetch('mode') == (root ? 'root' : 'build') && receipt.fetch('name') == mod &&
        receipt.fetch('sources_unchanged') == true && receipt.fetch('final_immutability_verified') == true &&
        receipt.fetch('bound_inputs_sha256').match?(/\A[0-9a-f]{64}\z/) &&
        reviewed_pairs.include?(receipt.values_at('tool_sha256', 'monitor_sha256')) &&
        receipt.values_at('source', 'source_sha256', 'compiled_object', 'compiled_sha256') ==
          binding.values_at('source', 'source_sha256', 'object', 'object_sha256'), 'A prerequisite has no genuine successful proof binding')
      next unless root
      snapshot_path = File.dirname(task + '/' + evidence) + '/SOURCE_HASHES.json'
      need(read_json.call(snapshot_path, receipt.fetch('source_hashes_sha256')) == sources,
        'Both root elaborations must bind the exact final full source/pin map')
    end
    validator_sha = bind.call(task + '/current-cache-validation.rb')
    contract = {
      'format' => 1, 'validator_sha256' => validator_sha, 'root' => ROOT, 'task' => task,
      'parent_run' => stage, 'original_cache' => ROOT + '/.publication-tools/twisted-e6-foundations-20261019/export',
      'lean_executable' => '/home/gerald/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean',
      'reviewed_verify_tool_pairs' => reviewed_pairs,
      'host_visibility_helper_sha256' => bind.call(task + '/cache-contract-builder.rb'),
      'parent_guard' => {'supervisor_pid' => Process.pid, 'supervisor_starttime' => starttime(Process.pid),
        'host_pid_namespace' => namespace, 'lease_device' => stat.dev, 'lease_inode' => stat.ino,
        'host_visibility_anchor' => visibility.fetch('anchor'),
        'monitor_sha256' => monitor_sha, 'owned_rss_cap_bytes' => 9 * 1024**3,
        'minimum_available_bytes' => 1024**3, 'combined_worker_ram_fraction' => [2, 3],
        'max_lean_workers' => 4, 'allocation_mib' => 8704},
      'anchors' => anchors,
      'historical_anchor_semantics' => 'Exact reviewed extant bytes; old receipts unchanged. No missing historical TSV SHA is invented.'
    }
    path = stage + '/CACHE_CONTRACT.json'
    File.open(path, File::WRONLY | File::CREAT | File::EXCL, 0o644) { |f| f.write(JSON.pretty_generate(contract) + "\n") }
    {contract: contract, path: path, sha256: bind.call(path), lease_fd: lease.fileno,
      output: stage + '/cache', validator_sha256: validator_sha}
  end
end
