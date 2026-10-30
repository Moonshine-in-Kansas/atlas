# SOURCE-ONLY PROPOSAL. Not installed, syntax-checked, or executed.
# No compiler/process/lease/watchdog implementation belongs in this file.
require 'json'
require 'digest'
require 'fileutils'
require 'set'
require 'stringio'
require 'time'
require 'zlib'

module AtlasAuditBatches
  PROTOCOL = 'atlas-registered-full-audit-batches-v1'.freeze
  AXIOMS = %w[propext Classical.choice Quot.sound].freeze
  PREFERRED_MIN = 32
  PREFERRED_MAX = 64
  MANIFEST_KEYS = %w[schema_version id imports mode definitions targets
    allowed_axioms boundaries environment original_manifest original_draft].freeze
  # One reviewed NEW policy already names canonical defining modules. This is
  # not an automatic rule for native targets, matching bytes, or absent receipts.
  CANONICAL_NEW_POLICY_SCOPE = 'verification/checkpoints/additions-20261030/f4-registration/f4-catalogue-identification-candidate.json'.freeze
  CANONICAL_NEW_POLICY_ORIGINAL = 'claude/release-update-v1.2-20261030/g2-catalogue/follow-up/f4-registration-candidate/manifests/f4-catalogue-identification-candidate.json'.freeze
  CANONICAL_NEW_POLICY_SHA256 = 'd974e678e363e5ee275499406eb828e99cc9e31440e18c2674e42648f398e0f6'.freeze

  def self.sha(path) = Digest::SHA256.file(path).hexdigest
  def self.bytes(object) = JSON.pretty_generate(object) + "\n"
  def self.scope_key(path) = 'scope-' + Digest::SHA256.hexdigest(path)[0, 24]

  # Plain bytes and their hash remain exact; gzip carries no current timestamp.
  def self.gzip_bytes(plain)
    buffer = StringIO.new(''.b)
    writer = Zlib::GzipWriter.new(buffer, Zlib::BEST_SPEED)
    writer.mtime = 0
    writer.write(plain)
    writer.finish
    buffer.string
  end

  def self.relative!(path)
    raise 'Unsafe relative artifact path' unless path.is_a?(String) &&
      !path.empty? && !path.start_with?('/') &&
      path.split('/').none? { |p| p.empty? || %w[. ..].include?(p) }
    path
  end

  # Registration/evidence inputs must not be redirected through a symlink.
  # The parent's intentionally shared package tree is handled by its own guards.
  def self.input_path(base, relative)
    path = File.join(File.expand_path(base), relative!(relative))
    cursor = File.expand_path(base)
    relative.split('/').each do |part|
      cursor = File.join(cursor, part)
      raise "Symlinked registration/evidence input #{cursor}" if File.symlink?(cursor)
    end
    raise "Missing input #{path}" unless File.file?(path)
    path
  end

  def self.read_bound(base, relative, digest)
    path = input_path(base, relative)
    data = File.binread(path)
    raise "Changed bound input #{relative}" unless Digest::SHA256.hexdigest(data) == digest
    [JSON.parse(data), data, path]
  end

  def self.target(t, remap = {})
    raise 'Unknown target fields' unless (t.keys - %w[declaration module source kind]).empty?
    mod = t['module'] ||
      t.fetch('source').delete_prefix('.lake/packages/mathlib/').delete_suffix('.lean').tr('/', '.')
    kind = t.fetch('kind')
    raise 'Unknown declaration kind' unless %w[any theorem definition].include?(kind)
    {'declaration' => t.fetch('declaration'), 'module' => remap.fetch(mod, mod), 'kind' => kind}
  end

  def self.full_manifest!(m)
    raise "Unsupported manifest fields #{m.keys - MANIFEST_KEYS}" unless (m.keys - MANIFEST_KEYS).empty?
    raise 'Full definitions/dependencies are mandatory' unless m['mode'] == 'full' && m['definitions'] == true
    raise 'Allowed axioms changed' unless m.fetch('allowed_axioms').sort == AXIOMS.sort
    refs = m.fetch('targets').map { |t| target(t) }
    names = refs.map { |r| r.fetch('declaration') }
    raise 'Empty or duplicate manifest roots' if refs.empty? || names.uniq != names
    refs
  end

  # Never discard an exact kind when another scope uses an any selector.
  def self.union_targets(manifests)
    selected = {}
    manifests.each do |manifest|
      full_manifest!(manifest).each do |t|
        name = t.fetch('declaration')
        old = selected[name]
        if old
          raise "Conflicting defining modules #{name}" unless old['module'] == t['module']
          kinds = [old['kind'], t['kind']].uniq - ['any']
          raise "Conflicting exact kinds #{name}" if kinds.length > 1
          selected[name] = old.merge('kind' => kinds.first || 'any')
        else
          selected[name] = t
        end
      end
    end
    selected.values.sort_by { |t| t.fetch('declaration') }
  end

  def self.origin_maps(merged)
    forward = {}; inverse = {}
    merged.fetch('sources').each do |source, row|
      canonical = row.fetch('module'); original = row.fetch('original_module')
      raise 'Canonical source/module mismatch' unless source == canonical.tr('.', '/') + '.lean'
      raise 'Source row identity mismatch' unless row.fetch('source') == source
      raise 'Ambiguous forward module map' if forward.key?(original) && forward[original] != canonical
      raise 'Ambiguous inverse module map' if inverse.key?(canonical) && inverse[canonical] != original
      forward[original] = canonical; inverse[canonical] = original
    end
    [forward.sort.to_h, inverse.sort.to_h]
  end

  def self.original_policy_view(registered, canonical_bytes, original_bytes)
    return 'source-origin' unless registered.fetch('manifest') == CANONICAL_NEW_POLICY_SCOPE
    expected = {'lane' => 'f4-registration', 'manifest' => CANONICAL_NEW_POLICY_SCOPE,
      'sha256' => CANONICAL_NEW_POLICY_SHA256,
      'original_manifest' => CANONICAL_NEW_POLICY_ORIGINAL,
      'original_manifest_sha256' => CANONICAL_NEW_POLICY_SHA256,
      'original_receipt' => nil, 'previous_mathematical_pass' => false,
      'target_count' => 11, 'candidate_environment' => 'verification/checkpoints/environment.json'}
    raise 'Canonical-new policy provenance changed' unless expected.all? { |k, v|
      registered.key?(k) && registered.fetch(k) == v } && registered['original_receipt_sha256'].nil?
    raise 'Canonical-new policy bytes changed' unless canonical_bytes == original_bytes &&
      Digest::SHA256.hexdigest(original_bytes) == CANONICAL_NEW_POLICY_SHA256
    'canonical-new-policy'
  end

  def self.original_policy_fields(scope)
    view = scope.fetch('original_policy_view')
    return {} if view == 'source-origin'
    raise 'Unknown original policy naming view' unless view == 'canonical-new-policy'
    {'original_policy_view' => view}
  end

  def self.inventory(task:, root:, merged:, environment:)
    forward, inverse = origin_maps(merged)
    seen = Set.new
    scopes = merged.fetch('scopes').map do |registered|
      path = registered.fetch('manifest')
      raise "Duplicate registered path #{path}" unless seen.add?(path)
      canonical, cbytes, cpath = read_bound(task + '/candidate', path, registered.fetch('sha256'))
      original, obytes, opath = read_bound(root, registered.fetch('original_manifest'),
        registered.fetch('original_manifest_sha256'))
      ctargets = full_manifest!(canonical)
      full_manifest!(original)
      view = original_policy_view(registered, cbytes, obytes)
      target_map = view == 'canonical-new-policy' ? {} : forward
      mapped = original.fetch('targets').map { |t| target(t, target_map) }
      raise "Original target coverage/order/kinds changed #{path}" unless mapped == ctargets
      raise 'Registered target count differs' unless registered.fetch('target_count') == ctargets.length
      raise 'Noncanonical import' unless canonical.fetch('imports').all? { |m| m.match?(/\AAtlas(?:\.[A-Za-z0-9_]+)*\z/) }
      envpath = canonical.fetch('environment')
      envfile = input_path(task + '/candidate', envpath)
      raise 'Manifest environment differs from candidate' unless JSON.parse(File.read(envfile)) == environment
      receipt = registered['original_receipt']
      receipt_binding = if receipt
        rp = input_path(root, receipt)
        raise 'Historical receipt changed' unless sha(rp) == registered.fetch('original_receipt_sha256')
        [rp, sha(rp)]
      end
      {
        'key' => scope_key(path), 'registered' => registered,
        'canonical' => canonical, 'original' => original,
        'canonical_bytes' => cbytes, 'original_bytes' => obytes,
        'original_policy_view' => view,
        'bindings' => [[cpath, registered['sha256']], [opath, registered['original_manifest_sha256']],
          [envfile, sha(envfile)], receipt_binding].compact
      }
    end
    raise 'Scope identity hash collision' unless scopes.map { |s| s['key'] }.uniq.length == scopes.length
    [scopes, inverse]
  end

  def self.subject(scope)
    registered = scope.fetch('registered')
    if registered['batch_subject']
      label = registered['batch_subject']
      raise 'Unsafe reviewed subject' unless label.match?(/\A[a-z0-9][a-z0-9-]*\z/)
      return label
    end
    lane = registered.fetch('lane')
    return 'f4' if %w[f4-comparison-policy-repair f4-registration].include?(lane)
    return 'twisted-e6' if lane == 'e6'
    return 'large-ree' if lane == 'ree'
    return 'g2-comparison' if lane == 'g2-catalogue'
    unless lane == 'j1-bridges'
      # New baseline-source companion scopes are real scopes too. Never omit
      # them merely because they introduce no new source or historical pass.
      label = lane.downcase.gsub(/[^a-z0-9-]/, '-')
      raise 'Empty subject lane' if label.empty?
      return 'lane-' + label
    end
    names = scope.fetch('canonical').fetch('targets').map { |t| t.fetch('declaration') }
    return 'j1' if names.any? { |n| n.start_with?('Atlas.Janko1.') }
    return 'ree-three' if names.any? { |n| n.start_with?('Atlas.ReeG2.', 'Atlas.Comparisons.ReeThree.') }
    'g2-binary'
  end

  # Read only the import header; ignore nested comments and documentation prose.
  def self.header_imports(text)
    pos = 0; names = []
    loop do
      if (m = /\G\s+/m.match(text, pos)); pos = m.end(0); next; end
      if text[pos, 2] == '--'; pos = text.index("\n", pos) || text.length; next; end
      if text[pos, 2] == '/-'
        pos += 2; depth = 1
        while depth.positive?
          a = text.index('/-', pos); b = text.index('-/', pos)
          raise 'Unclosed import header comment' unless b
          if a && a < b; depth += 1; pos = a + 2; else depth -= 1; pos = b + 2; end
        end
        next
      end
      m = /\G(?:public\s+|private\s+)?import[ \t]+/.match(text, pos)
      break unless m
      pos = m.end(0)
      stop = text.index("\n", pos) || text.length
      comment = text.index('--', pos); stop = comment if comment && comment < stop
      row = text[pos...stop].split
      raise 'Unexpected import header syntax' unless row.all? { |n| n.match?(/\A[A-Za-z_][A-Za-z0-9_.]*\z/) }
      names.concat(row); pos = stop
    end
    names
  end

  def self.import_fingerprint(candidate, manifest, memo)
    todo = manifest.fetch('imports').dup; seen = Set.new
    until todo.empty?
      mod = todo.pop
      next unless mod.start_with?('Atlas.') && seen.add?(mod)
      memo[mod] ||= header_imports(File.read(input_path(candidate, mod.tr('.', '/') + '.lean')))
      todo.concat(memo.fetch(mod))
    end
    seen
  end

  # Pure planning: no proof processes, policies, caches or evidence are executed.
  def self.plan(task:, root:)
    merged_path = input_path(task, 'MERGED_SOURCES.json')
    environment_path = input_path(task, 'CANDIDATE_ENVIRONMENT.json')
    merged = JSON.parse(File.read(merged_path)); environment = JSON.parse(File.read(environment_path))
    scopes, = inventory(task: task, root: root, merged: merged, environment: environment)
    memo = {}
    fingerprints = scopes.to_h { |s| [s['key'], import_fingerprint(task + '/candidate', s['canonical'], memo)] }
    groups = []
    scopes.group_by { |s| subject(s) }.sort.each do |label, members|
      remaining = members.sort_by { |s| [-s['canonical']['targets'].size, s['registered']['manifest']] }
      until remaining.empty?
        group = [remaining.shift]
        if group.first['canonical']['targets'].length <= PREFERRED_MAX
          loop do
            current = union_targets(group.map { |s| s['canonical'] })
            fingerprint = group.reduce(Set.new) { |a, s| a | fingerprints.fetch(s['key']) }
            choices = remaining.filter_map do |s|
              union = union_targets((group + [s]).map { |x| x['canonical'] })
              next if union.length > PREFERRED_MAX
              overlap = (fingerprint & fingerprints.fetch(s['key'])).size
              root_overlap = current.length + s['canonical']['targets'].length - union.length
              [s, overlap, root_overlap, union.length]
            end
            break if choices.empty?
            chosen = choices.sort_by { |s, overlap, roots, size| [-overlap, -roots, -size, s['registered']['manifest']] }.first.first
            group << chosen; remaining.delete(chosen)
          end
        end
        groups << [label, group]
      end
    end
    # F4 first, then alternate subjects; leave no automatic same-run memory retry.
    priority = %w[f4 large-ree twisted-e6 g2-comparison j1 g2-binary ree-three]
    queues = groups.group_by(&:first); ordered = []
    priority += queues.keys.sort - priority
    while queues.values.any? { |q| !q.empty? }
      priority.each { |s| ordered << queues[s].shift if queues[s] && !queues[s].empty? }
    end
    files = {}; batches = []
    ordered.each_with_index do |(label, members), i|
      id = format('batch-%03d-%s', i + 1, label)
      refs = union_targets(members.map { |s| s['canonical'] })
      manifest = {
        'schema_version' => 1, 'id' => id, 'mode' => 'full', 'definitions' => true,
        'allowed_axioms' => AXIOMS, 'boundaries' => [],
        'environment' => 'verification/checkpoints/environment.json',
        'imports' => members.flat_map { |s| s['canonical']['imports'] }.uniq.sort,
        'targets' => refs
      }
      path = 'batch-manifests/' + id + '.json'; files[path] = bytes(manifest)
      batches << {'id' => id, 'subject' => label, 'manifest' => path,
        'sha256' => Digest::SHA256.hexdigest(files[path]),
        'scopes' => members.map { |s| s['registered']['manifest'] },
        'targets' => refs.length, 'whole_oversized_original' => refs.length > PREFERRED_MAX,
        'small_batch_reason' => refs.length < PREFERRED_MIN ? 'Whole same-subject scopes do not fit another batch under the 64-target preference.' : nil}
    end
    registry = {
      'format' => 1, 'protocol' => PROTOCOL,
      'merged_sources' => {'path' => 'MERGED_SOURCES.json', 'sha256' => sha(merged_path)},
      'environment' => {'path' => 'CANDIDATE_ENVIRONMENT.json', 'sha256' => sha(environment_path)},
      'scope_inventory' => merged.fetch('scopes'),
      'scope_count' => scopes.length,
      'required_policies' => scopes.flat_map { |s|
        r = s['registered']
        [{'id' => 'canonical-' + s['key'], 'kind' => 'successor', 'scope' => r['manifest'],
          'manifest' => r['manifest'], 'sha256' => r['sha256']},
         {'id' => 'original-' + s['key'], 'kind' => 'source-transported', 'scope' => r['manifest'],
          'manifest' => r['original_manifest'], 'sha256' => r['original_manifest_sha256']}.merge(original_policy_fields(s))]
      },
      'grouping' => {'preferred_min' => PREFERRED_MIN, 'preferred_max' => PREFERRED_MAX,
        'split_original_scopes' => false, 'safety_limit' => 'Parent adaptive memory/worker monitor; target count is not a safety limit.',
        'heuristic' => 'Subject first, then static transitive Atlas-import overlap; this is not measured dependency-graph overlap.'},
      'producer_bindings' => nil,
      'registration_status' => 'proposal-parent-must-bind-reviewed-producer',
      'batches' => batches
    }
    files['BATCH_REGISTRY.json'] = bytes(registry)
    [registry, files]
  end

  # Parent calls this under its already-held shared lease and live watchdog.
  # guard must also attest that common source/cache/environment guards succeeded.
  def self.load_registered!(task:, root:, candidate:, registry_path:, batch_path:, merged:, environment:, stage:, guard:)
    raise 'Missing parent guarded callback' unless guard.respond_to?(:call)
    guard.call(:registration)
    task = File.expand_path(task); root = File.expand_path(root)
    candidate = File.expand_path(candidate); stage = File.expand_path(stage)
    raise 'Wrong canonical candidate' unless candidate == task + '/candidate'
    raise 'Wrong parent stage' unless stage.start_with?(task + '/verification-runs/') && File.directory?(stage)
    raise 'Wrong fixed registry' unless File.expand_path(registry_path) == task + '/BATCH_REGISTRY.json'
    registry_file = input_path(task, 'BATCH_REGISTRY.json')
    registry_bytes = File.binread(registry_file); registry = JSON.parse(registry_bytes)
    raise 'Unknown batch protocol' unless registry.values_at('format', 'protocol') == [1, PROTOCOL]
    raise 'Unreviewed registration' unless registry.fetch('registration_status') == 'registered-parent-reviewed'
    raise 'Wrong inventory/environment registration paths' unless registry.fetch('merged_sources').fetch('path') == 'MERGED_SOURCES.json' &&
      registry.fetch('environment').fetch('path') == 'CANDIDATE_ENVIRONMENT.json'
    observed, _, merged_file = read_bound(task, registry.fetch('merged_sources').fetch('path'), registry['merged_sources']['sha256'])
    raise 'Parent/registry merged inventory differs' unless observed == merged
    raise 'Omitted, added or changed scope inventory' unless registry.fetch('scope_inventory') == merged.fetch('scopes') &&
      registry.fetch('scope_count') == merged.fetch('scopes').length
    current_env, _, envfile = read_bound(task, registry.fetch('environment').fetch('path'), registry['environment']['sha256'])
    raise 'Parent environment differs' unless current_env == environment
    producer = registry.fetch('producer_bindings')
    raise 'Parent has not bound the reviewed batch producer' unless producer.is_a?(Hash) && !producer.empty?
    required_tools = %w[verify monitor batch_helper policy]
    raise 'Incomplete producer bindings' unless producer.keys.sort == required_tools.sort
    tool_bindings = producer.map do |_name, p|
      base = p.fetch('base') == 'task' ? task : p.fetch('base') == 'root' ? root : (raise 'Unknown producer base')
      file = input_path(base, p.fetch('path'))
      raise 'Changed producer/helper/policy' unless sha(file) == p.fetch('sha256')
      [file, p['sha256']]
    end
    helper = producer.fetch('batch_helper')
    raise 'Registered helper is not this helper' unless helper.fetch('base') == 'task' &&
      File.realpath(input_path(task, helper.fetch('path'))) == File.realpath(__FILE__)
    raise 'Unexpected verifier/monitor/policy paths' unless
      producer.fetch('verify').values_at('base', 'path') == %w[task verify.rb] &&
      producer.fetch('monitor').values_at('base', 'path') == %w[task monitor.rb] &&
      producer.fetch('policy').values_at('base', 'path') == %w[root verification/tools/policy.rb]
    scopes, inverse = inventory(task: task, root: root, merged: merged, environment: environment)
    by_path = scopes.to_h { |s| [s['registered']['manifest'], s] }
    batches = registry.fetch('batches')
    raise 'Unsafe batch identity' unless batches.all? { |b| b.fetch('id').match?(/\Abatch-[0-9]{3,}-[a-z0-9-]+\z/) }
    raise 'Duplicate batch identities/paths' unless batches.map { |b| b['id'] }.uniq.size == batches.size &&
      batches.map { |b| b['manifest'] }.uniq.size == batches.size
    covered = batches.flat_map { |b| b.fetch('scopes') }
    raise 'Every scope must occur exactly once' unless covered.sort == by_path.keys.sort
    expected_policies = scopes.flat_map do |s|
      r = s['registered']
      [{'id' => 'canonical-' + s['key'], 'kind' => 'successor', 'scope' => r['manifest'],
        'manifest' => r['manifest'], 'sha256' => r['sha256']},
       {'id' => 'original-' + s['key'], 'kind' => 'source-transported', 'scope' => r['manifest'],
        'manifest' => r['original_manifest'], 'sha256' => r['original_manifest_sha256']}.merge(original_policy_fields(s))]
    end
    raise 'Missing or weakened original/successor policy inventory' unless registry.fetch('required_policies') == expected_policies
    bindings = [[registry_file, Digest::SHA256.hexdigest(registry_bytes)],
      [merged_file, registry['merged_sources']['sha256']], [envfile, registry['environment']['sha256']]] + tool_bindings
    selected = nil; union = nil
    batches.each do |batch|
      m, raw, path = read_bound(task, batch.fetch('manifest'), batch.fetch('sha256'))
      members = batch.fetch('scopes').map { |p| by_path.fetch(p) }
      raise 'Empty extraction batch' if members.empty?
      refs = union_targets(members.map { |s| s['canonical'] })
      expected = {'schema_version' => 1, 'id' => batch.fetch('id'), 'mode' => 'full',
        'definitions' => true, 'allowed_axioms' => AXIOMS, 'boundaries' => [],
        'environment' => 'verification/checkpoints/environment.json',
        'imports' => members.flat_map { |s| s['canonical']['imports'] }.uniq.sort, 'targets' => refs}
      raise 'Union manifest is not exactly its registered scopes' unless m == expected
      raise 'Batch target count differs' unless refs.length == batch.fetch('targets')
      oversized_original = members.any? { |s| s.fetch('canonical').fetch('targets').size > PREFERRED_MAX }
      raise 'Whole oversized original scopes must remain individual' if oversized_original && members.length != 1
      raise 'Wrong oversized original annotation' unless batch.fetch('whole_oversized_original') == oversized_original
      if refs.length > PREFERRED_MAX && !oversized_original
        reason = batch['preference_exception_reason']
        raise 'Record the reviewed grouping preference exception' unless reason.is_a?(String) && !reason.strip.empty?
      end
      raise 'Batch crosses subjects' unless members.map { |s| subject(s) }.uniq == [batch.fetch('subject')]
      bindings << [path, Digest::SHA256.hexdigest(raw)]
      if File.expand_path(batch_path) == path
        selected = batch; union = m
      end
    end
    raise 'Batch path is not uniquely registered' unless selected
    bindings.concat(scopes.flat_map { |s| s['bindings'] })
    merged.fetch('sources').each_value do |row|
      original = input_path(root, row.fetch('original_source'))
      raise 'Original source changed' unless sha(original) == row.fetch('original_sha256')
      bindings << [original, row.fetch('original_sha256')]
    end
    {
      task: task, root: root, candidate: candidate, stage: stage, guard: guard,
      registry: registry, registry_bytes: registry_bytes, batch: selected,
      manifest: union, scopes: selected['scopes'].map { |p| by_path.fetch(p) },
      inverse: inverse, merged: merged, bindings: bindings.uniq,
      started_utc: Time.now.utc.iso8601
    }
  end

  # Emit after registration, before extraction, so failed/stopped attempts also
  # have an unambiguous locator. This is a locator, never a success receipt.
  def self.announce_stage!(context)
    puts 'ATLAS_AUDIT_BATCH_STAGE ' + JSON.generate(
      protocol: PROTOCOL, batch: context.fetch(:batch).fetch('id'),
      invocation: ENV['ATLAS_BATCH_INVOCATION'], stage: context.fetch(:stage))
    $stdout.flush
  end

  def self.unchanged!(context)
    context.fetch(:guard).call(:input_recheck)
    context.fetch(:bindings).each do |path, digest|
      raise "Registered input/tool changed during extraction #{path}" unless sha(path) == digest
    end
  end

  def self.declarations_match!(declarations, targets)
    raise 'Missing, duplicate or extra declarations' unless declarations.map { |d| d.fetch('declaration') }.sort ==
      targets.map { |t| t.fetch('declaration') }.sort
    by_name = declarations.to_h { |d| [d.fetch('declaration'), d] }
    targets.each do |t|
      d = by_name.fetch(t.fetch('declaration'))
      raise 'Wrong compiled defining module' unless d.fetch('module') == t.fetch('module')
      kind = t.fetch('kind')
      raise 'Wrong compiled kind' unless kind == 'any' ||
        (kind == 'theorem' && d.fetch('theorem') == true) ||
        (kind == 'definition' && d.fetch('theorem') == false)
    end
  end

  def self.graph_shape!(graph)
    raise 'Empty full graph' if graph.empty?
    graph.each do |name, node|
      raise 'Graph key/name mismatch' unless name == node.fetch('name')
      %w[type value dependencies].each do |key|
        raise 'Missing full type/value dependency edges' unless node.fetch(key).is_a?(Array) &&
          node[key].all? { |n| n.is_a?(String) }
      end
      raise 'Type/value edges omitted from closure edges' unless
        ((node['type'] + node['value']) - node['dependencies']).empty?
    end
  end

  def self.inverse_collision_check!(graph, declarations, inverse)
    modules = graph.values.flat_map { |n| [n.fetch('module'), n['source_module']].compact }
    modules.concat(declarations.flat_map { |d| [d.fetch('module'), d['source_module']].compact })
    modules.uniq!
    raise 'Origin transport collides with an unchanged module' unless
      modules.map { |m| inverse.fetch(m, m) }.uniq.size == modules.size
  end

  # Bind the supplied in-memory objects to the one actual extractor output.
  # Only one graph is kept; this streaming comparison creates no second graph.
  def self.extraction_bindings!(stage, graph, declarations)
    declaration_file = input_path(stage, 'declarations.jsonl')
    observed = File.foreach(declaration_file).map { |line| JSON.parse(line) }
    raise 'Supplied declarations differ from actual extraction' unless observed == declarations
    graph_file = input_path(stage, 'dependencies.jsonl')
    seen = Set.new
    File.foreach(graph_file) do |line|
      node = JSON.parse(line); name = node.fetch('name')
      raise 'Duplicate actual graph node' unless seen.add?(name)
      raise 'Supplied graph differs from actual extraction' unless node == graph.fetch(name)
    end
    raise 'Supplied graph includes unextracted nodes' unless seen.size == graph.size
    [[declaration_file, sha(declaration_file)], [graph_file, sha(graph_file)]]
  end

  def self.transported_metadata(row, inverse)
    result = row.merge('module' => inverse.fetch(row.fetch('module'), row.fetch('module')))
    result['source_module'] = inverse.fetch(row['source_module'], row['source_module']) if row.key?('source_module')
    result
  end

  def self.write_new(stage, relative, content)
    relative!(relative)
    cursor = File.expand_path(stage)
    raise 'Symlinked evidence stage' if File.symlink?(cursor)
    relative.split('/')[0...-1].each do |part|
      cursor = File.join(cursor, part)
      raise 'Symlinked evidence directory' if File.symlink?(cursor)
    end
    path = File.join(stage, relative)
    raise "Preserve existing evidence #{relative}" if File.exist?(path) || File.symlink?(path)
    FileUtils.mkdir_p(File.dirname(path))
    File.open(path, File::WRONLY | File::CREAT | File::EXCL, 0o644) { |io| io.binmode; io.write(content); io.flush; io.fsync }
    path
  end

  # This is a validation of the untouched producer, NOT a process-record adapter.
  def self.process_binding!(context, process_path, log_path, targets)
    stage = File.expand_path(context.fetch(:stage))
    [process_path, log_path].each do |p|
      raise 'Foreign process artifact' unless File.expand_path(p).start_with?(stage + '/')
      input_path(stage, File.expand_path(p).delete_prefix(stage + '/'))
    end
    process = JSON.parse(File.read(process_path))
    raise 'Unsuccessful extraction process' unless process['status'] == 'process-passed' &&
      process['exit_code'] == 0 && process['signal'].nil? && process['guard_stop'].nil? &&
      process.fetch('proof_diagnostic_errors') == false && !process['failure'] &&
      process.fetch('diagnostic_examples', []).empty?
    start = Time.iso8601(process.fetch('started_utc')); finish = Time.iso8601(process.fetch('finished_utc'))
    raise 'Process predates this registered batch' unless start >= Time.iso8601(context.fetch(:started_utc)) && finish >= start
    raw_digest = Digest::SHA256.new
    printed = []; marker_count = 0
    io = log_path.end_with?('.gz') ? Zlib::GzipReader.open(log_path) : File.open(log_path, 'rb')
    begin
      io.each_line do |line|
        raw_digest.update(line)
        raise 'Error/PANIC/sorry in extraction log' if line.match?(/\berror(?:\([^\n]*\))?:|\bPANIC\b|\bsorry\b/)
        marker_count += 1 if line.strip == "SHARED EXTRACTION COMPLETE: #{targets.length} targets"
        m = line.match(/\ASTATEMENT (\S+) SOURCE (\S+)\s*\z/)
        printed << [m[1], m[2]] if m
      end
    ensure
      io.close
    end
    expected_digest = process['log_plain_sha256'] || process.fetch('log_sha256')
    raise 'Original process/log hash differs' unless raw_digest.hexdigest == expected_digest
    raise 'Conflicting producer log aliases' if process['log_sha256'] && process['log_sha256'] != expected_digest
    if log_path.end_with?('.gz')
      raise 'Original compressed log hash differs' unless sha(log_path) == process.fetch('log_compressed_sha256')
      raise 'Original process did not confirm gzip recovery' unless process.fetch('log_recovery_verified') == true
    end
    raise 'Incomplete or duplicate extraction marker' unless marker_count == 1
    raise 'Missing/duplicated printed compiled statement' unless printed.sort ==
      targets.map { |t| t.values_at('declaration', 'module') }.sort
    process
  end

  # Called only AFTER the parent's post-extraction guards have passed.
  # The parent's watchdog and shared lease must continue through this return.
  # No successful scope result is written until every member's two policies pass.
  def self.finalize!(context:, graph:, declarations:, manifest:, merged:, stage:, process_path:, log_path:)
    raise 'Wrong supplied parent stage/manifest/source registry' unless stage == context[:stage] &&
      manifest == context[:manifest] && merged == context[:merged]
    unchanged!(context)
    raise 'Parent must inject its pinned policy helper' unless defined?(AtlasVerification)
    targets = manifest.fetch('targets')
    declarations_match!(declarations, targets)
    graph_shape!(graph)
    inverse_collision_check!(graph, declarations, context.fetch(:inverse))
    extraction_bindings = extraction_bindings!(stage, graph, declarations)
    context[:bindings].concat(extraction_bindings)
    original_process = process_binding!(context, process_path, log_path, targets)
    context[:bindings].concat([[process_path, sha(process_path)], [log_path, sha(log_path)]])
    union_outcome = AtlasVerification.check_policy(manifest, declarations, graph)
    raise 'Union unexpectedly has subject-specific restrictions' unless union_outcome.empty? && manifest['boundaries'] == []
    by_name = declarations.to_h { |d| [d.fetch('declaration'), d] }
    process_sha = sha(process_path)
    pending = {}; scope_rows = []; policy_rows = []
    before_path = input_path(stage, 'SOURCE_HASHES.json')
    after_path = input_path(stage, 'SOURCE_HASHES_AFTER.json')
    before = JSON.parse(File.read(before_path)); after = JSON.parse(File.read(after_path))
    raise 'Parent before/after exact export bindings differ' unless before == after
    stage_merged = input_path(stage, 'MERGED_SOURCES.json')
    raise 'Parent archived inventory differs' unless sha(stage_merged) == context[:registry]['merged_sources']['sha256']
    context[:bindings].concat([[before_path, sha(before_path)], [after_path, sha(after_path)],
      [stage_merged, sha(stage_merged)]])
    archives = merged.fetch('sources').values.sort_by { |r| r.fetch('module') }.to_h do |row|
      raise 'Origin map has stale canonical source' unless before.fetch(row.fetch('source')) == row.fetch('sha256')
      data = File.binread(input_path(context[:root], row.fetch('original_source')))
      raise 'Original source archive differs' unless Digest::SHA256.hexdigest(data) == row.fetch('original_sha256')
      path = 'ORIGINAL_SOURCES/' + row.fetch('original_sha256') + '.lean'
      pending[path] = data
      [row.fetch('module'), {'path' => path, 'sha256' => row.fetch('original_sha256')}]
    end
    # These exact-byte provenance members are shared once at publication bundle
    # root. They are source archives, not a private package or job-document export.
    inverse_document = {'format' => 1, 'modules' => context[:inverse],
      'merged_sources' => 'MERGED_SOURCES.json',
      'merged_sources_sha256' => context[:registry]['merged_sources']['sha256'],
      'source_hashes' => 'SOURCE_HASHES.json', 'source_hashes_sha256' => sha(before_path),
      'original_sources' => archives}
    inverse_bytes = bytes(inverse_document)
    inverse_sha = Digest::SHA256.hexdigest(inverse_bytes)
    uncompressed_hashes = {'dependencies.jsonl' => extraction_bindings.last.last}
    if log_path.end_with?('.gz')
      uncompressed_hashes[File.expand_path(log_path).delete_prefix(stage + '/').delete_suffix('.gz')] =
        original_process['log_plain_sha256'] || original_process.fetch('log_sha256')
    end
    canonical_axioms = declarations.flat_map { |d| d.fetch('axioms') }.uniq.sort
    context[:scopes].each do |scope|
      context.fetch(:guard).call(:scoped_policy)
      key = scope.fetch('key'); canonical = scope.fetch('canonical'); original = scope.fetch('original')
      canonical_targets = full_manifest!(canonical)
      # Preserve optional canonical source fields exactly: portable checkpoint
      # validation compares this roots artifact with the unchanged manifest.
      roots = canonical.fetch('targets')
      chosen = roots.map { |t| by_name.fetch(t.fetch('declaration')) }
      declarations_match!(chosen, canonical_targets)
      names = AtlasVerification.closure(graph, roots.map { |t| t.fetch('declaration') }).to_a.sort
      slice = names.to_h { |name| [name, graph.fetch(name)] }
      canonical_outcome = AtlasVerification.check_policy(canonical, chosen, slice)
      # Keep the complete global source-origin map and its collision guard.
      # Only this registered new policy uses identity module metadata; every
      # historical policy (including native-target policies) retains the inverse.
      policy_inverse = scope.fetch('original_policy_view') == 'canonical-new-policy' ? {} : context[:inverse]
      original_records = chosen.map { |d| transported_metadata(d, policy_inverse) }
      original_graph = slice.transform_values { |n| transported_metadata(n, policy_inverse) }
      declarations_match!(original_records, full_manifest!(original))
      raise 'Module transport changed exact root closure' unless
        AtlasVerification.closure(original_graph, roots.map { |t| t.fetch('declaration') }).to_a.sort == names
      original_outcome = AtlasVerification.check_policy(original, original_records, original_graph)
      dir = 'scopes/' + key
      checkpoint_path = dir + '/CHECKPOINT.json'; original_path = dir + '/ORIGINAL.json'
      slice_path = dir + '/dependency_slice.json.gz'
      slice_plain = bytes(names); slice_bytes = gzip_bytes(slice_plain)
      uncompressed_hashes[slice_path.delete_suffix('.gz')] = Digest::SHA256.hexdigest(slice_plain)
      policies = ['canonical-' + key, 'original-' + key]
      policy_rows << {'id' => policies[0], 'kind' => 'successor', 'manifest' => checkpoint_path,
        'sha256' => Digest::SHA256.hexdigest(scope.fetch('canonical_bytes'))}
      policy_rows << {'id' => policies[1], 'kind' => 'source-transported', 'manifest' => original_path,
        'sha256' => Digest::SHA256.hexdigest(scope.fetch('original_bytes')),
        'origin_map' => 'ORIGIN_MODULES.json', 'origin_map_sha256' => inverse_sha}.merge(original_policy_fields(scope))
      outcomes = [canonical_outcome, original_outcome]
      policies_map = policies.each_with_index.to_h do |id, i|
        row = policy_rows[-2 + i]
        outcome = {'status' => 'passed', 'manifest_sha256' => row.fetch('sha256'),
          'targets' => roots.length, 'dependency_nodes' => slice.length, 'boundaries' => outcomes[i]}
        if i == 1
          outcome['origin_map_sha256'] = inverse_sha
          outcome.merge!(original_policy_fields(scope))
        end
        [id, outcome]
      end
      scope_result = {'status' => 'passed', 'mode' => 'full', 'checkpoint' => canonical.fetch('id'),
        'targets' => roots.length, 'dependency_nodes' => slice.length,
        'axioms' => chosen.flat_map { |d| d.fetch('axioms') }.uniq.sort,
        'boundaries' => canonical_outcome, 'batch' => context[:batch]['id'],
        'batch_process_sha256' => process_sha,
        'dependency_slice_sha256' => Digest::SHA256.hexdigest(slice_bytes),
        'dependency_slice_uncompressed_sha256' => uncompressed_hashes.fetch(slice_path.delete_suffix('.gz')),
        'started_utc' => original_process.fetch('started_utc'), 'finished_utc' => Time.now.utc.iso8601,
        'fresh_project_rebuild' => false, 'independent_replay' => false}
      pending[checkpoint_path] = scope.fetch('canonical_bytes')
      pending[original_path] = scope.fetch('original_bytes')
      pending[dir + '/roots.json'] = bytes(roots)
      pending[slice_path] = slice_bytes
      pending[dir + '/POLICY_RESULTS.json'] = bytes(policies_map)
      pending[dir + '/FULL_RESULT.json'] = bytes(scope_result)
      scope_rows << {'id' => key, 'roots' => dir + '/roots.json', 'checkpoint' => checkpoint_path,
        'result' => dir + '/FULL_RESULT.json', 'policies' => policies,
        'policy_results' => dir + '/POLICY_RESULTS.json', 'batch' => context[:batch]['id'],
        'dependency_slice' => slice_path}
      # Do not retain another scope's transported graph.
      slice = nil; original_graph = nil; original_records = nil; slice_plain = nil
    end
    batch_result = {'status' => 'passed', 'mode' => 'full', 'checkpoint' => manifest.fetch('id'),
      'targets' => targets.length, 'dependency_nodes' => graph.length,
      'boundaries' => union_outcome, 'axioms' => canonical_axioms,
      'started_utc' => original_process.fetch('started_utc'), 'finished_utc' => Time.now.utc.iso8601,
      'original_process_sha256' => process_sha, 'fresh_project_rebuild' => false, 'independent_replay' => false}
    raw_process_name = File.expand_path(process_path).delete_prefix(stage + '/')
    raw_log_name = File.expand_path(log_path).delete_prefix(stage + '/')
    batch_row = {'id' => context[:batch]['id'], 'roots' => 'roots.json',
      'checkpoint' => 'BATCH_CHECKPOINT.json', 'result' => 'BATCH_FULL_RESULT.json',
      'record' => raw_process_name, 'log' => raw_log_name,
      'declarations' => 'declarations.jsonl', 'dependencies' => 'dependencies.jsonl.gz',
      'source_hashes' => 'SOURCE_HASHES.json', 'source_hashes_after' => 'SOURCE_HASHES_AFTER.json'}
    pending['roots.json'] = bytes(targets)
    pending['BATCH_CHECKPOINT.json'] = bytes(manifest)
    pending['BATCH_FULL_RESULT.json'] = bytes(batch_result)
    pending['ORIGIN_MODULES.json'] = inverse_bytes
    pending['POLICIES.json'] = bytes({'format' => 1, 'entries' => policy_rows})
    evidence = {'format' => 1, 'protocol' => PROTOCOL,
      'batch' => batch_row, 'scopes' => scope_rows, 'policy_inventory' => 'POLICIES.json',
      'uncompressed_hashes' => uncompressed_hashes.sort.to_h,
      'shared_provenance_members' => (['MERGED_SOURCES.json', 'SOURCE_HASHES.json', 'ORIGIN_MODULES.json'] +
        archives.values.map { |a| a.fetch('path') }).uniq.sort,
      'registry_sha256' => Digest::SHA256.hexdigest(context[:registry_bytes]),
      'registered_batch_sha256' => context[:batch]['sha256'],
      'original_process' => {'path' => raw_process_name, 'sha256' => process_sha},
      'parent_result' => 'RESULT.json', 'parent_result_required_status' => 'passed-full-canonical-batch-audit',
      'publication_adapter_required' => 'Banach lossless process/parent-result binding adapter; original artifacts must remain unchanged.',
      'normal_proof_checks_supplied' => false, 'new_additions_acceptance_claimed' => false}
    unchanged!(context)
    pending.each do |p, data|
      path = write_new(stage, p, data)
      context[:bindings] << [path, Digest::SHA256.hexdigest(data)]
    end
    unchanged!(context)
    # Commit the index last. Collectors must also require the successful original
    # parent RESULT.json with this file's digest; orphaned fragments are not passes.
    evidence_path = write_new(stage, 'BATCH_EVIDENCE.json', bytes(evidence))
    context[:bindings] << [evidence_path, sha(evidence_path)]
    {evidence_path: evidence_path, evidence_sha256: sha(evidence_path),
      targets: targets.length, scopes: scope_rows.length, dependency_nodes: graph.length,
      bound_files: context[:bindings].to_h}
  end
end
