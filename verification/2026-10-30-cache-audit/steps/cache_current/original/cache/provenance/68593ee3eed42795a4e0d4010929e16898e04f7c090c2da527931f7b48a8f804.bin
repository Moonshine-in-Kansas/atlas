#!/usr/bin/env ruby
# SOURCE-ONLY PROPOSAL. Parent reviews and runs this only after 266 proofs + 2 roots.
# This program never invokes Lean/Lake, evaluates proofs, acquires a lease, or
# changes the candidate/cache/index. Runtime subprocesses are read-only Git only.
require 'json'
require 'digest'
require 'fileutils'
require 'optparse'
require 'open3'
require 'time'
require 'zlib'

module CurrentCacheValidation
  BASELINE_COUNT = 4865
  NEW_COUNT = 266
  OBJECT_COUNT = 5133
  ROOTS = %w[Atlas Atlas.Audit].freeze
  PINS = %w[lean-toolchain lakefile.toml lake-manifest.json].freeze
  FIELDS = %w[source source_sha256 object object_sha256 basis evidence].freeze
  OLD_LICENCE = 'Released under Apache 2.0 license as described in the file LICENSE.'
  PUBLIC_LICENCE = 'Released under the ATLAS Research and Attribution License 1.0; see LICENSE.'
  LICENCE_APPROVAL = 'Approved ATLAS-owned licence notice only; proof text and line count unchanged'
  SHA = /\A[0-9a-f]{64}\z/
  MODULE = /\AAtlas(?:\.[A-Za-z0-9_]+)*\z/
  OPTIONS = %w[-j1 -M8704 -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false
               -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3].freeze
  LEGACY_TOOL = 'ef7b21e3c2a6307400a19e1062316d5808a4f9cbd5505d440ce203573c21673f'
  LEGACY_MONITOR = 'f4c115f13884ff36cea47942977837f18778add04b8ad0cc445f3dd859e1baa6'

  class Failure < StandardError; end
  class UniqueHash < Hash
    def []=(key, value)
      raise Failure, "Duplicate JSON key #{key}" if key?(key)
      super
    end
  end

  class Validator
    def need(condition, message)
      raise Failure, message unless condition
    end

    def parse(bytes)
      JSON.parse(bytes, object_class: UniqueHash)
    end

    def relative(path)
      need(path.is_a?(String) && !path.empty? && !path.start_with?('/') &&
        path.split('/').none? { |s| s.empty? || %w[. ..].include?(s) } &&
        !path.include?("\0"), "Nonportable relative path #{path.inspect}")
      path
    end

    def inside(base, rel)
      File.join(base, relative(rel))
    end

    # Sources, receipts and candidate objects may not escape through symlinks.
    # Dependency-package symlinks are handled separately by packages!.
    def ordinary(path)
      path = File.expand_path(path)
      need(File.realpath(path) == path && File.file?(path), "Nonordinary input #{path}")
      path
    end

    def digest(path)
      Digest::SHA256.file(ordinary(path)).hexdigest
    end

    def initialize(contract_path, output)
      @contract_path = File.expand_path(contract_path)
      raw = File.binread(ordinary(@contract_path))
      @contract_sha = Digest::SHA256.hexdigest(raw)
      need(ENV.fetch('ATLAS_CACHE_CONTRACT_SHA256').match?(SHA) &&
        ENV.fetch('ATLAS_CACHE_CONTRACT_SHA256') == @contract_sha,
        'Contract must be byte-pinned by the reviewing parent')
      @contract = parse(raw)
      need(@contract.fetch('format') == 1, 'Unsupported parent contract')
      @validator_sha = digest(__FILE__)
      need(@contract.fetch('validator_sha256') == @validator_sha,
        'Validator bytes are not the parent-reviewed proposal')
      @root = File.realpath(@contract.fetch('root'))
      @task = File.realpath(@contract.fetch('task'))
      need(@task == @root + '/claude/release-update-v1.2-20261030', 'Wrong task')
      @candidate = File.realpath(@task + '/candidate')
      @original_cache = File.realpath(@contract.fetch('original_cache'))
      need(@original_cache == @root + '/.publication-tools/twisted-e6-foundations-20261019/export',
        'Wrong original cache origin')
      @out = File.expand_path(output)
      parent_run = @contract.fetch('parent_run')
      need(File.dirname(parent_run) == @task + '/verification-runs' &&
        File.basename(parent_run).match?(/\A\d{8}T\d{6}-cache-current-current\z/) &&
        File.realpath(parent_run) == parent_run && @out == parent_run + '/cache' && !File.exist?(@out),
        'Output must be the new cache child of the actual parent cache-current run')
      @lean = @contract.fetch('lean_executable')
      need(@lean == '/home/gerald/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean',
        'Wrong recorded compiler identity')
      @bound = {@contract_path => @contract_sha, File.expand_path(__FILE__) => @validator_sha}
      @written = {}
      @provenance = {}
      @anchors = {}
      @origins = {}
      @edge_maps = {}
      @guard = @contract.fetch('parent_guard')
      @host_helper_sha = @contract.fetch('host_visibility_helper_sha256')
      host_helper = @task + '/cache-contract-builder.rb'
      bind(host_helper, @host_helper_sha, archive: false)
      require host_helper
      fd = Integer(ENV.fetch('ATLAS_CACHE_LEASE_FD'), 10)
      need(fd >= 3, 'An inherited lease descriptor is required')
      @lease = IO.for_fd(fd, autoclose: false)
      @lease_fd = fd
      guard!
      FileUtils.mkdir_p(File.dirname(@out))
      need(File.realpath(File.dirname(@out)) == File.dirname(@out), 'Output parent is a symlink')
      Dir.mkdir(@out)
      @started = Time.now.utc.iso8601
    end

    def process_start(pid)
      # Fields after the comm field start at stat field 3; starttime is field 22.
      File.read("/proc/#{pid}/stat").sub(/\A\d+ \(.*\) /, '').split.fetch(19)
    end

    def guard!
      parent = @guard.fetch('supervisor_pid')
      need(parent.is_a?(Integer) && parent == Process.ppid, 'Not a direct monitored child')
      need(process_start(parent) == @guard.fetch('supervisor_starttime'), 'Supervisor identity changed')
      visibility = AtlasCurrentCacheContract.observe_host!
      need(visibility.fetch('anchor') == @guard.fetch('host_visibility_anchor'), 'Live host anchor differs from the parent contract')
      namespace = visibility.fetch('observer').fetch('pid_namespace')
      need(namespace == @guard.fetch('host_pid_namespace') &&
        namespace == File.readlink("/proc/#{parent}/ns/pid"), 'Child/supervisor namespace differs from the owned desktop anchor')
      parent_status = File.read("/proc/#{parent}/status")
      need(AtlasCurrentCacheContract.status_numbers(parent_status, 'Uid') == [1000] * 4 &&
        AtlasCurrentCacheContract.status_numbers(parent_status, 'NSpid') == [parent], 'Supervisor UID/namespace depth changed')
      lock = @root + '/verification/chevalley/.runner.lock'
      need(!File.symlink?(lock), 'Lease pathname is a symlink')
      s = File.stat(lock)
      inherited = @lease.stat
      need([s.dev, s.ino] == [inherited.dev, inherited.ino] &&
        [s.dev, s.ino] == @guard.values_at('lease_device', 'lease_inode'), 'Wrong inherited lease')
      info = File.read("/proc/self/fdinfo/#{@lease_fd}")
      lock_line = info.lines.find do |line|
        line.match?(/\Alock:\s+\d+: FLOCK\s+ADVISORY\s+WRITE\s+#{parent}\s+/) &&
          line.split[-3].split(':').last.to_i == s.ino && line.split.last(2) == %w[0 EOF]
      end
      need(lock_line, 'Descriptor is not the parent-owned exclusive FLOCK')
      need(@guard.fetch('monitor_sha256').match?(SHA) &&
        digest(@task + '/monitor.rb') == @guard.fetch('monitor_sha256'), 'Parent monitor changed')
      need(@guard.fetch('owned_rss_cap_bytes') == 9 * 1024**3 &&
        @guard.fetch('minimum_available_bytes') == 1024**3 &&
        @guard.fetch('combined_worker_ram_fraction') == [2, 3] &&
        @guard.fetch('max_lean_workers') == 4 && @guard.fetch('allocation_mib') == 8704,
        'Parent must retain the existing host guard')
      available = File.read('/proc/meminfo')[/^MemAvailable:\s+(\d+)/, 1]
      need(available && available.to_i * 1024 >= 1024**3, 'Actual RAM reserve reached')
      @last_guard = {'supervisor_pid' => parent, 'supervisor_starttime' => process_start(parent),
        'host_pid_namespace' => namespace, 'inherited_fd' => @lease_fd,
        'lease_device' => s.dev, 'lease_inode' => s.ino, 'fdinfo_lock' => lock_line.strip,
        'host_visibility_anchor' => visibility.fetch('anchor'), 'host_observer' => visibility.fetch('observer')}
      # Intentionally no flock/open-new-lock/unlock/close operation here.
    end

    def write_bytes(member, bytes)
      path = inside(@out, member)
      FileUtils.mkdir_p(File.dirname(path))
      File.open(path, File::WRONLY | File::CREAT | File::EXCL, 0o644) { |f| f.write(bytes) }
      @written[member] = Digest::SHA256.hexdigest(bytes)
      member
    end

    def write_json(member, value)
      write_bytes(member, JSON.pretty_generate(value) + "\n")
    end

    # Content-addressed provenance is copied verbatim, never rewritten as a pass.
    def bind(path, expected = nil, archive: true)
      path = ordinary(path)
      hash = digest(path)
      need(expected.nil? || (expected.match?(SHA) && hash == expected), "Hash mismatch #{path}")
      need(!@bound.key?(path) || @bound[path] == hash, "Input changed #{path}")
      @bound[path] = hash
      if archive
        member = 'provenance/' + hash + '.bin'
        unless @written.key?(member)
          FileUtils.mkdir_p(File.dirname(inside(@out, member)))
          File.open(inside(@out, member), File::WRONLY | File::CREAT | File::EXCL, 0o644) do |dst|
            File.open(path, 'rb') { |src| IO.copy_stream(src, dst) }
          end
          need(digest(inside(@out, member)) == hash, "Input changed while archiving #{path}")
          @written[member] = hash
        end
        @provenance[path] = {'member' => member, 'sha256' => hash}
      end
      hash
    end

    def document(path, expected = nil)
      hash = bind(path, expected)
      bytes = File.binread(path)
      need(Digest::SHA256.hexdigest(bytes) == hash, "Document changed #{path}")
      parse(bytes)
    end

    def anchor(name, required_path = nil, json: true)
      a = @contract.fetch('anchors').fetch(name)
      path = File.expand_path(a.fetch('path'), @root)
      need(required_path.nil? || path == required_path, "Wrong #{name} anchor path")
      need(path.start_with?(@root + '/'), 'Anchor escaped checkout')
      value = json ? document(path, a.fetch('sha256')) : bind(path, a.fetch('sha256'))
      @anchors[name] = @provenance.fetch(path)
      value
    end

    def source_paths
      (Dir.glob(@candidate + '/Atlas/**/*.lean') + [@candidate + '/Atlas.lean']).sort.map do |p|
        ordinary(p).delete_prefix(@candidate + '/')
      end
    end

    def source_snapshot
      (source_paths + PINS).sort.to_h do |p|
        guard! if (@source_tick = (@source_tick || 0) + 1) % 100 == 0
        [p, digest(inside(@candidate, p))]
      end
    end

    def object_snapshot
      files = (Dir.glob(@candidate + '/.lake/build/lib/lean/Atlas/**/*.olean') +
        [@candidate + '/.lake/build/lib/lean/Atlas.olean']).sort
      files.each_with_index.to_h do |p, i|
        guard! if i % 25 == 0
        need(File.stat(ordinary(p)).nlink == 1, "Object is not an independent file #{p}")
        [p.delete_prefix(@candidate + '/'), digest(p)]
      end
    end

    def identity(b)
      FIELDS.map { |k| b.fetch(k) }
    end

    # Only the import header is parsed, not Lean declarations or proof terms.
    # Unrecognised import syntax fails rather than silently omitting an edge.
    def import_header(bytes)
      depth = 0
      header = []
      bytes.force_encoding(Encoding::UTF_8).each_line do |line|
        clean = +''
        i = 0
        while i < line.length
          pair = line[i, 2]
          if pair == '/-'
            depth += 1; i += 2
          elsif depth > 0 && pair == '-/'
            depth -= 1; i += 2
          elsif depth > 0
            i += 1
          elsif pair == '--'
            break
          else
            clean << line[i]; i += 1
          end
        end
        clean = clean.strip
        next if clean.empty? || %w[prelude module].include?(clean)
        if clean.match?(/\A(?:public\s+|private\s+)?import\b/)
          match = clean.match(/\A(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\z/)
          need(match, 'Unsupported import header syntax')
          header.concat(match[1].split)
        else
          break
        end
      end
      need(depth == 0, 'Unclosed source-header comment')
      header.grep(/\AAtlas(?:\.|\z)/).uniq
    end

    def closure(module_name)
      found = {}
      todo = @imports.fetch(module_name).dup
      until todo.empty?
        m = todo.pop
        need(m != module_name, "Atlas import cycle involving #{module_name}")
        next if found.key?(m)
        need(@index.key?(m), "Unbound imported module #{m}")
        found[m] = true
        todo.concat(@imports.fetch(m))
      end
      found.keys.sort
    end

    def packages!
      expected = @environment.fetch('revisions')
      packages = @manifest.fetch('packages')
      names = packages.map { |p| p.fetch('name') }
      need(names.uniq == names && names.all? { |n| n.match?(/\A[A-Za-z0-9_-]+\z/) }, 'Invalid package names')
      need(packages.to_h { |p| ['.lake/packages/' + p['name'], p.fetch('rev')] } == expected,
        'Package manifest/environment revision mismatch')
      need(File.realpath(@candidate + '/.lake/packages') == File.realpath(@root + '/.lake/packages'),
        'Candidate package link points elsewhere')
      expected.sort.to_h do |rel, rev|
        guard!
        dir = File.realpath(inside(@root, rel))
        need(rev.match?(/\A[0-9a-f]{40}\z/), 'Invalid pinned revision')
        env = {'GIT_OPTIONAL_LOCKS' => '0', 'GIT_TERMINAL_PROMPT' => '0',
          'GIT_NO_LAZY_FETCH' => '1', 'GIT_LFS_SKIP_SMUDGE' => '1'}
        git = ['git', '--no-optional-locks', '-c', 'core.fsmonitor=false',
          '-c', 'core.untrackedCache=false', '-C', dir]
        head, err, status = Open3.capture3(env, *git, 'rev-parse', '--verify', 'HEAD')
        need(status.success? && head.strip == rev, "Wrong package revision #{rel}: #{err}")
        dirty, err, status = Open3.capture3(env, *git, 'status', '--porcelain=v1',
          '--untracked-files=all', '--ignore-submodules=none')
        need(status.success? && dirty.empty?, "Dirty package #{rel}: #{err} #{dirty}")
        # Ignored package build caches are not advertised as independently verified.
        [rel, {'revision' => head.strip, 'working_tree_clean' => true,
          'untracked_nonignored_clean' => true, 'resolved_path' => dir}]
      end
    end

    def process_receipt!(dir, result, command)
      need(result.fetch('process_receipt') == 'process.json', 'Unexpected process receipt name')
      process = document(dir + '/process.json', result.fetch('process_receipt_sha256'))
      need(process.fetch('status') == 'process-passed' && process.fetch('exit_code') == 0 &&
        process.fetch('signal').nil? && process.fetch('guard_stop').nil? && process['failure'].nil? &&
        process.fetch('proof_diagnostic_errors') == false && process.fetch('log_recovery_verified') == true,
        "Unsuccessful process #{dir}")
      need(process.fetch('command') == command && process.fetch('cwd') == @candidate,
        "Wrong actual process invocation #{dir}")
      need(process.fetch('environment') == @process_env, 'Process package search path changed')
      gz = dir + '/process.log.gz'
      bind(gz, process.fetch('log_compressed_sha256'))
      plain = Digest::SHA256.new
      hash_passes = []
      Zlib::GzipReader.open(gz) do |z|
        z.each_line do |line|
          plain.update(line)
          need(!line.match?(/\berror(?:\([^\n]*\))?:|PANIC at|declaration uses ['`]sorry['`]/),
            'Diagnostic failure in actual process log')
          hash_passes << line.strip if line.start_with?('PASS: ')
        end
      end
      need(plain.hexdigest == process.fetch('log_plain_sha256'), 'Process log recovery mismatch')
      [process, hash_passes]
    end

    def baseline!
      inventory = anchor('CACHE_ARTIFACTS', @task + '/cache-preparation/CACHE_ARTIFACTS.json')
      preparation = anchor('CACHE_PREPARATION_RESULT', @task + '/cache-preparation/RESULT.json')
      tsv_path = @task + '/cache-preparation/CACHE_HASHES.tsv'
      anchor('CACHE_HASHES_TSV', tsv_path, json: false)
      need(preparation['status'] == 'baseline-cache-copied-and-trace-hash-verified' &&
        preparation['candidate_cache_has_independent_copies'] == true &&
        preparation['baseline_modules'] == BASELINE_COUNT && inventory.size == BASELINE_COUNT &&
        preparation['root_modules_excluded_for_fresh_elaboration'].sort == ROOTS.sort,
        'Invalid baseline cache preparation')
      reference = preparation.fetch('trace_hash_verification')
      receipt_path = File.expand_path(reference.fetch('receipt'), @root)
      need(receipt_path == @task + '/verification-runs/20261030T042504-cache-hashes-baseline/RESULT.json' &&
        reference['status'] == 'passed-baseline-trace-hash-check', 'Wrong authentic baseline validation')
      result = anchor('BASELINE_HASH_RESULT', receipt_path)
      need(result['status'] == 'passed-baseline-trace-hash-check' && result['mode'] == 'cache-hashes' &&
        result['candidate'] == @candidate && result['sources_unchanged'] == true &&
        result['fresh_whole_project_rebuild'] == false && result['independent_replay'] == false &&
        result['tool_sha256'] == LEGACY_TOOL && result['monitor_sha256'] == LEGACY_MONITOR,
        'Historical cache validation is not the authentic recorded pass')
      dir = File.dirname(receipt_path)
      checker = dir + '/CacheHashes.lean'
      anchor('BASELINE_HASH_CHECKER', checker, json: false)
      _process, passes = process_receipt!(dir, result, [@lean, '-j1', '-M1024', '--run', checker, tsv_path])
      need(passes == ["PASS: #{BASELINE_COUNT * 2} Lake source/artifact hashes match the original build traces."],
        'Historical trace-hash coverage differs')
      then_sources = document(dir + '/SOURCE_HASHES.json', result.fetch('source_hashes_sha256'))
      licence = anchor('LICENCE_BINDING', @candidate + '/verification/release-candidate/LICENCE_BINDING.json')
      old_map = anchor('HISTORICAL_CACHE_SOURCE_HASHES',
        @candidate + '/verification/2026-10-26-cache-audit/CACHE_SOURCE_HASHES.json')
      %w[verification/release-candidate/LICENCE_BINDING.json
         verification/2026-10-26-cache-audit/CACHE_SOURCE_HASHES.json].each do |p|
        need(@bound.fetch(@candidate + '/' + p) == @baseline.fetch(p),
          "Historical published provenance was modified: #{p}")
      end
      need(inventory.map { |e| e.fetch('source') }.sort == @baseline_paths &&
        inventory.map { |e| e['source'] }.uniq.size == BASELINE_COUNT, 'Incomplete/duplicate baseline inventory')
      expected_tsv = +''
      @original_sources = {}
      @compatibility = {}
      inventory.sort_by { |e| e.fetch('source') }.each_with_index do |entry, i|
        guard! if i % 50 == 0
        src = entry.fetch('source')
        mod = src.delete_suffix('.lean').tr('/', '.')
        binding = @index.fetch(mod)
        need(binding['basis'] == 'validated-published-baseline-cache' &&
          binding['evidence'] == 'cache-preparation/CACHE_ARTIFACTS.json', "Wrong baseline provenance #{mod}")
        need(entry.fetch('candidate_source_sha256') == @sources.fetch(src) &&
          then_sources.fetch(src) == @sources.fetch(src) && @baseline.fetch(src) == @sources.fetch(src),
          "Changed published baseline source #{src}")
        need(entry.fetch('compiled_object') == @candidate + '/' + binding.fetch('object') &&
          entry.fetch('compiled_sha256') == @objects.fetch(binding.fetch('object')), 'Baseline object drift')
        original_path = inside(@original_cache, src)
        need(entry.fetch('cache_source') == original_path, 'Wrong original source path')
        bind(original_path, entry.fetch('source_sha256'), archive: false)
        need(old_map.fetch(src) == entry['source_sha256'], 'Original cache source provenance differs')
        original = File.binread(original_path)
        published = File.binread(inside(@candidate, src))
        transformation = entry.fetch('transformation')
        if transformation == 'byte-identical'
          need(original == published, 'False byte-identical cache claim')
        else
          need(transformation == 'previously-approved-licence-comment-substitution', 'Unapproved source transformation')
          proof = licence.fetch(src)
          need(proof.values_at('original_sha256', 'export_sha256', 'change') ==
            [entry['source_sha256'], @sources.fetch(src), LICENCE_APPROVAL], 'Missing exact approved licence provenance')
          header = original[/\A\s*\/-.*?-\//m]
          need(header && header.include?(OLD_LICENCE) && original.scan(OLD_LICENCE).size == 1 &&
            original.sub(OLD_LICENCE, PUBLIC_LICENCE) == published && original.lines.size == published.lines.size,
            'Difference is not the exact approved header-comment substitution')
          # Preserve the original nonidentical source itself for portable review.
          bind(original_path, entry['source_sha256'])
        end
        trace_path = inside(@original_cache, '.lake/build/lib/lean/' + src.delete_suffix('.lean') + '.trace')
        need(entry.fetch('historical_trace') == trace_path, 'Wrong original trace path')
        trace = document(trace_path, entry.fetch('trace_sha256'))
        need(trace['synthetic'] == false, 'Synthetic historical trace')
        source_inputs = trace.fetch('inputs').select { |x| x.is_a?(Array) && x[0] == @root + '/' + src }
        need(source_inputs.size == 1 && source_inputs[0][1].is_a?(String) &&
          source_inputs[0][1].match?(/\A[0-9a-f]{16}\z/), 'Missing unique historical source hash')
        o = trace.fetch('outputs').fetch('o')
        need(o.is_a?(Array) && o.size == 1 && o[0].match?(/\A[0-9a-f]{16}\.olean\z/), 'Wrong old trace output')
        expected_tsv << ['text', original_path, source_inputs[0][1]].join("\t") + "\n"
        expected_tsv << ['binary', entry['compiled_object'], o[0].delete_suffix('.olean')].join("\t") + "\n"
        @original_sources[src] = entry['source_sha256']
        @compatibility[src] = {'current_source_sha256' => @sources[src],
          'original_compiled_source_sha256' => entry['source_sha256'], 'transformation' => transformation,
          'licence_provenance' => transformation == 'byte-identical' ? nil : @anchors.fetch('LICENCE_BINDING')}
        @origins[mod] = {'basis' => binding['basis'], 'compiled_source_sha256' => entry['source_sha256'],
          'current_compatible_source_sha256' => @sources[src], 'object_sha256' => entry['compiled_sha256'],
          'original_trace' => @provenance.fetch(trace_path), 'historical_hash_check' => @anchors.fetch('BASELINE_HASH_RESULT')}
      end
      need(File.binread(tsv_path) == expected_tsv, 'Historical TSV is not the exact authentic trace inventory')
      @original_pins = PINS.to_h do |p|
        original = inside(@original_cache, p)
        [p, bind(original, old_map.fetch(p))]
      end
      need(@original_pins['lean-toolchain'] == @sources['lean-toolchain'] &&
        @original_pins['lake-manifest.json'] == @sources['lake-manifest.json'], 'Old toolchain/dependency pins differ')
      old_package = File.binread(@original_cache + '/lakefile.toml')
      current_package = File.binread(@candidate + '/lakefile.toml')
      need(old_package.scan(/^version = "0\.1\.0"$/).size == 1 &&
        old_package.sub(/^version = "0\.1\.0"$/, 'version = "1.2.0"') == current_package,
        'Package metadata difference is not solely the recorded published version change')
      @compatibility['lakefile.toml'] = {'transformation' => 'published-package-version-only-0.1.0-to-1.2.0',
        'original_sha256' => @original_pins['lakefile.toml'], 'current_sha256' => @sources['lakefile.toml'],
        'published_baseline_provenance' => @anchors.fetch('BASELINE_EXPORT')}
      @historical_limits = [
        'The old hash-check receipt names its TSV but lacks a TSV SHA field. ',
        'The reviewing parent must authenticate and pin the unchanged TSV/inventory/trace/source bundle; ',
        'this run compares that pinned TSV exactly to the unchanged authentic traces and source/object SHA maps. ',
        'It does not invent a missing historical hash binding or rerun Lake.computeFileHash.'
      ].join
    end

    def fresh!(mod)
      guard!
      b = @index.fetch(mod)
      need(b['basis'] == 'fresh-canonical-proof-check', "No fresh proof provenance #{mod}")
      evidence = relative(b.fetch('evidence'))
      need(evidence.match?(%r{\Averification-runs/[^/]+/RESULT\.json\z}), 'Receipt outside genuine parent runs')
      result_path = inside(@task, evidence)
      r = document(result_path)
      dir = File.dirname(result_path)
      root = ROOTS.include?(mod)
      need(r['status'] == 'passed-fresh-canonical-proof-check' && r['mode'] == (root ? 'root' : 'build') &&
        r['name'] == mod && r['candidate'] == @candidate && r['canonical_package'] == true &&
        r['root_integration'] == root && r['source_to_object_bindings_verified'] == true &&
        r['sources_unchanged'] == true && r['final_immutability_verified'] == true &&
        r['fresh_whole_project_rebuild'] == false && r['independent_replay'] == false &&
        r['failure'].nil? && r['ruby_guard_stop'].nil?, "Not a successful reviewed verify.rb receipt #{mod}")
      need(r.values_at('source', 'source_sha256', 'compiled_object', 'compiled_sha256') ==
        b.values_at('source', 'source_sha256', 'object', 'object_sha256'), 'Receipt/source/object identity differs')
      pair = [r.fetch('tool_sha256'), r.fetch('monitor_sha256')]
      need(@contract.fetch('reviewed_verify_tool_pairs').include?(pair), 'Unreviewed verifier/monitor bytes')
      bind(dir + '/verification-driver.rb', pair[0])
      bind(dir + '/process-monitor.rb', pair[1])
      snapshot = document(dir + '/SOURCE_HASHES.json', r.fetch('source_hashes_sha256'))
      saved = document(dir + '/IMPORTED_OBJECTS.json', r.fetch('imported_objects_sha256'))
      need(saved.keys.sort == closure(mod), "Incomplete imported-object closure #{mod}")
      saved.each do |dep, prior|
        need(identity(prior) == identity(@index.fetch(dep)), "Changed dependency identity #{mod} -> #{dep}")
      end
      relevant = ([b.fetch('source')] + saved.values.map { |entry| entry.fetch('source') } + PINS).uniq.sort
      relevant.each do |path|
        need(snapshot.fetch(path) == @sources.fetch(path), "Checked source/import/pin changed #{mod}: #{path}")
      end
      need(!root || snapshot == @sources, 'Root receipt must bind the exact final full source snapshot')
      environment = document(dir + '/ENVIRONMENT.json', r.fetch('environment_sha256'))
      need(environment == @environment && r.fetch('dependency_revisions') == @revisions, 'Proof environment differs')
      merge_path = dir + '/MERGED_SOURCES.json'
      historical_merge = document(merge_path, r.fetch('integration_registry_sha256'))
      historical_merge.fetch('sources').each do |path, entry|
        need(entry.fetch('source') == path && entry.fetch('module') == path.delete_suffix('.lean').tr('/', '.') &&
          entry.fetch('sha256') == snapshot.fetch(path), 'Original registry disagrees with its original snapshot')
      end
      relevant.each do |path|
        next unless @merged.fetch('sources').key?(path)
        need(historical_merge.fetch('sources').fetch(path).values_at('source', 'module', 'sha256') ==
          @merged.fetch('sources').fetch(path).values_at('source', 'module', 'sha256'),
          "Original checked/imported source identity differs #{mod}: #{path}")
      end
      need(!root || historical_merge == @merged, 'Root registry must match the final current registry')
      bounds = document(dir + '/BOUND_INPUTS.json', r.fetch('bound_inputs_sha256'))
      required = {dir + '/SOURCE_HASHES.json' => r['source_hashes_sha256'],
        @task + '/MERGED_SOURCES.json' => r['integration_registry_sha256'],
        @task + '/CANDIDATE_ENVIRONMENT.json' => @bound.fetch(@task + '/CANDIDATE_ENVIRONMENT.json'),
        @task + '/verify.rb' => pair[0], @task + '/monitor.rb' => pair[1]}
      need(required.all? { |p,h| bounds[p] == h } && bounds.fetch(@task + '/OBJECT_BINDINGS.json').match?(SHA),
        'Incomplete genuine bound-input/finalization record')
      command = [@lean, *OPTIONS, '--root=' + @candidate, '-o', @candidate + '/' + b['object'],
        '-i', @candidate + '/' + b['object'].delete_suffix('.olean') + '.ilean', @candidate + '/' + b['source']]
      process_receipt!(dir, r, command)
      member = 'import-edges/' + mod + '.json'
      write_json(member, saved.sort.to_h)
      @edge_maps[mod] = {'member' => member, 'sha256' => @written.fetch(member), 'edge_count' => saved.size,
        'actual_original_snapshot' => @provenance.fetch(dir + '/IMPORTED_OBJECTS.json')}
      @origins[mod] = {'basis' => b['basis'], 'compiled_source_sha256' => b['source_sha256'],
        'current_compatible_source_sha256' => b['source_sha256'], 'object_sha256' => b['object_sha256'],
        'normal_or_root_result' => @provenance.fetch(result_path), 'mode' => r['mode'],
        'receipt_binding_scope' => root ? 'exact-final-full-snapshot' : 'own-source-transitive-imports-pins-revisions',
        'original_full_snapshot_sha256' => r.fetch('source_hashes_sha256'),
        'original_integration_registry_sha256' => r.fetch('integration_registry_sha256'),
        'original_full_snapshot_equals_current' => snapshot == @sources,
        'import_edges' => @edge_maps.fetch(mod)}
    end

    def run
      bind(__FILE__, @validator_sha)
      bind(@task + '/cache-contract-builder.rb', @host_helper_sha)
      @baseline = anchor('BASELINE_EXPORT', @task + '/BASELINE_EXPORT.json').fetch('files')
      @index = anchor('OBJECT_BINDINGS', @task + '/OBJECT_BINDINGS.json')
      @merged = anchor('MERGED_SOURCES', @task + '/MERGED_SOURCES.json')
      order = anchor('INTEGRATION_ORDER', @task + '/INTEGRATION_ORDER.json')
      @environment = anchor('CANDIDATE_ENVIRONMENT', @task + '/CANDIDATE_ENVIRONMENT.json')
      expected_sources = anchor('CURRENT_SOURCE_HASHES')
      @sources = source_snapshot
      need(@sources == expected_sources, 'Current source snapshot differs from parent-pinned final snapshot')
      @objects = object_snapshot
      paths = @sources.keys.grep(/\.lean\z/).sort
      @baseline_paths = @baseline.keys.grep(%r{\AAtlas/.*\.lean\z}).reject { |p| p == 'Atlas/Audit.lean' }.sort
      @new_paths = @merged.fetch('sources').keys.sort
      root_paths = ROOTS.map { |m| m.tr('.', '/') + '.lean' }
      need(@baseline_paths.size == BASELINE_COUNT && @new_paths.size == NEW_COUNT &&
        (@new_paths & @baseline.keys).empty? && paths == (@baseline_paths + @new_paths + root_paths).sort &&
        paths.size == OBJECT_COUNT, 'Expected exactly 4865 baseline + 266 new + 2 root sources')
      @baseline_paths.each { |p| need(@sources[p] == @baseline[p], "Baseline mathematics changed #{p}") }
      need(@sources.fetch('Atlas/Audit.lean') == @baseline.fetch('Atlas/Audit.lean'),
        'The current task preserves the published Audit root bytes; fresh elaboration is still required')
      PINS.each { |p| need(@sources[p] == @baseline[p] && @sources[p] == @environment.fetch('pins').fetch(p), 'Public pin changed') }
      need(order.fetch('new_sources') == NEW_COUNT && order.fetch('source_build_order').sort ==
        @new_paths.map { |p| p.delete_suffix('.lean').tr('/', '.') }.sort, 'Integration order lacks exact new sources')
      @merged.fetch('sources').each do |p, e|
        need(e.fetch('source') == p && e.fetch('module') == p.delete_suffix('.lean').tr('/', '.') &&
          e.fetch('sha256') == @sources[p], "Unbound merged source #{p}")
      end
      expected_modules = paths.map { |p| p.delete_suffix('.lean').tr('/', '.') }.sort
      need(@index.keys.sort == expected_modules && @index.size == OBJECT_COUNT, 'Object index incomplete or contains extras')
      expected_artifacts = expected_modules.map { |m| '.lake/build/lib/lean/' + m.tr('.', '/') + '.olean' }.sort
      need(@objects.keys.sort == expected_artifacts, 'Current cache object file set is not exact')
      @index.each do |m,b|
        need(m.match?(MODULE) && b.fetch('source') == m.tr('.', '/') + '.lean' &&
          b.fetch('object') == '.lake/build/lib/lean/' + m.tr('.', '/') + '.olean' &&
          b.fetch('source_sha256') == @sources.fetch(b['source']) &&
          b.fetch('object_sha256') == @objects.fetch(b['object']), "Stale source/object binding #{m}")
      end
      @imports = @index.to_h { |m,b| [m, import_header(File.binread(inside(@candidate,b['source'])))] }
      @imports.each { |m,deps| deps.each { |d| need(@index.key?(d), "Missing Atlas import #{m} -> #{d}") } }
      @manifest = parse(File.binread(@candidate + '/lake-manifest.json'))
      @revisions = @manifest.fetch('packages').to_h { |p| [p.fetch('name'),p.fetch('rev')] }
      @process_env = {'LEAN_NUM_THREADS' => '2', 'LEAN_PATH' =>
        ([@candidate + '/.lake/build/lib/lean'] + @manifest['packages'].reverse.map { |p|
          @root + '/.lake/packages/' + p.fetch('name') + '/.lake/build/lib/lean' }).join(':')}
      package_before = packages!
      baseline!
      (order.fetch('source_build_order') + ROOTS).each { |m| fresh!(m) }
      need(@origins.keys.sort == expected_modules, 'Provenance coverage is not the whole current cache')
      write_json('SOURCE_HASHES.json', @sources)
      write_json('CACHE_SOURCE_HASHES.json', @sources)
      write_json('CACHE_ARTIFACTS.json', @objects)
      write_json('OBJECT_BINDINGS.json', @index)
      write_json('ORIGINAL_CACHE_SOURCE_HASHES.json', @original_sources.merge(@original_pins).sort.to_h)
      write_json('ORIGINAL_CACHE_ENVIRONMENT.json', {'pins' => @original_pins, 'dependency_revisions' => @revisions,
        'scope' => '4865 original cached module sources plus actual original package pins; excludes old roots not reused.'})
      write_json('COMPILED_SOURCE_HASHES.json', @origins.to_h { |m,e| [m.tr('.', '/') + '.lean',e['compiled_source_sha256']] }.sort.to_h)
      write_json('SOURCE_COMPATIBILITY.json', @compatibility.sort.to_h)
      write_json('OBJECT_ORIGINS.json', @origins.sort.to_h)
      write_json('IMPORTED_OBJECT_EDGES.json', @edge_maps.sort.to_h)
      after_sources = source_snapshot
      after_objects = object_snapshot
      package_after = packages!
      need(after_sources == @sources && after_objects == @objects && package_before == package_after,
        'Source, cache or dependency package changed during integrity validation')
      @bound.each_with_index do |(path, hash),i|
        guard! if i % 100 == 0
        need(digest(path) == hash, "Provenance/registry/original source changed during validation #{path}")
      end
      write_json('SOURCE_HASHES_AFTER.json', after_sources)
      write_json('CACHE_ARTIFACTS_AFTER.json', after_objects)
      write_json('PACKAGES_BEFORE.json', package_before)
      write_json('PACKAGES_AFTER.json', package_after)
      write_json('PROVENANCE.json', @provenance.sort.to_h)
      write_json('INPUT_BINDINGS.json', @bound.sort.to_h)
      @written.each_with_index do |(member, hash),i|
        guard! if i % 100 == 0
        need(digest(inside(@out, member)) == hash, "Generated payload changed: #{member}")
      end
      guard!
      record = {'format' => 1, 'status' => 'validated-current-cache-integrity-child-result',
        'started_utc' => @started, 'finished_utc' => Time.now.utc.iso8601,
        'scope' => 'Actual current SHA integrity and genuine source/object provenance for all 5133 Atlas objects; no proof execution.',
        'counts' => {'baseline_objects' => BASELINE_COUNT, 'new_normal_proofs' => NEW_COUNT, 'fresh_root_elaborations' => 2,
          'objects' => OBJECT_COUNT, 'source_and_pin_entries' => @sources.size},
        'source_binding_semantics' => 'Exact current compatible-source bytes, not an assertion that historical compiled sources/comments/package version were identical.',
        'original_compiled_source_map' => 'COMPILED_SOURCE_HASHES.json',
        'original_baseline_cache_source_map' => 'ORIGINAL_CACHE_SOURCE_HASHES.json',
        'historical_trace_hash_binding_limit' => @historical_limits,
        'sources_unchanged' => true, 'cache_artifacts_unchanged' => true,
        'fresh_whole_project_rebuild' => false, 'fresh_project_rebuild' => false,
        'independent_replay' => false, 'new_proof_build' => false, 'new_full_dependency_audit' => false,
        'current_cache_integrity_validation_performed' => true, 'new_lake_hash_evaluation_performed' => false,
        'original_receipts_unchanged' => true, 'parent_monitor_finalization_required' => true,
        'parent_finalization_rule' => 'Accept only with a separate genuine monitor process-passed receipt and parent final RESULT binding this CACHE_BINDING SHA. Never accept child status alone.',
        'tool_sha256' => @validator_sha, 'parent_contract_sha256' => @contract_sha, 'inherited_held_lease' => @last_guard,
        'anchors' => @anchors, 'files' => @written.sort.to_h}
      write_json('CACHE_BINDING.json', record)
      puts JSON.generate(status: record['status'], cache_binding_sha256: @written.fetch('CACHE_BINDING.json'),
        objects: OBJECT_COUNT, parent_monitor_finalization_required: true)
      0
    rescue StandardError => e
      if @out && Dir.exist?(@out) && !File.exist?(@out + '/CACHE_BINDING.json')
        write_json('FAILURE.json', {'status' => 'not-passed', 'failure' => e.message,
          'finished_utc' => Time.now.utc.iso8601, 'fresh_whole_project_rebuild' => false, 'independent_replay' => false})
      end
      warn "Current cache validation failed: #{e.class}: #{e.message}"
      1
    end
  end
end

if $PROGRAM_NAME == __FILE__
  opts = {}
  parser = OptionParser.new do |p|
    p.banner = 'Parent only: ruby current-cache-validation.rb --contract FILE --out NEW_RUN_DIRECTORY'
    p.on('--contract FILE') { |v| opts[:contract] = v }
    p.on('--out DIRECTORY') { |v| opts[:out] = v }
  end
  begin
    parser.parse!
    raise CurrentCacheValidation::Failure, parser.to_s unless opts.keys.sort == %i[contract out] && ARGV.empty?
    exit CurrentCacheValidation::Validator.new(opts[:contract], opts[:out]).run
  rescue StandardError => e
    warn "Current cache validator refused to start: #{e.class}: #{e.message}"
    exit 1
  end
end
