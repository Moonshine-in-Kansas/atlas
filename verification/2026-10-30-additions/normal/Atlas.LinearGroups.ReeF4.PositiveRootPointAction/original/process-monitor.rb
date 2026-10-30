require 'json'
require 'digest'
require 'fileutils'
require 'time'
require 'zlib'

module ReleasePreparationMonitor
  ROOT = '/home/gerald/atlas'
  def self.memory
    text = File.read('/proc/meminfo')
    %w[MemTotal MemAvailable SwapFree].to_h { |name| [name, text[/^#{name}:\s+(\d+)/, 1].to_i * 1024] }
  end

  def self.workers(group = nil)
    result = {owned_rss: 0, owned_swap: 0, combined_rss: 0, owned_lean: 0, total_lean: 0}
    Dir['/proc/[0-9]*/stat'].each do |path|
      begin
        fields = File.read(path).sub(/\A\d+ \(.*\) /, '').split
        text = File.read(path.sub(/stat$/, 'status'))
        name = text[/^Name:\s+(\S+)/, 1]
        rss = text[/^VmRSS:\s+(\d+)/, 1].to_i * 1024
        result[:combined_rss] += rss if %w[codex lean lake ruby].include?(name)
        result[:total_lean] += 1 if name == 'lean'
        if group && fields[2].to_i == group
          result[:owned_rss] += rss
          result[:owned_swap] += text[/^VmSwap:\s+(\d+)/, 1].to_i * 1024
          result[:owned_lean] += 1 if name == 'lean'
        end
      rescue Errno::ENOENT, Errno::ESRCH, Errno::EACCES
      end
    end
    result
  end

  def self.stop(pid)
    Process.kill('TERM', -pid) rescue Errno::ESRCH
    sleep 1
    Process.kill('KILL', -pid) rescue Errno::ESRCH
  end

  def self.run(directory, name, command, env:, cwd:, held_lease: nil)
    FileUtils.mkdir_p(directory)
    receipt = directory + '/' + name + '.json'
    raise 'Preserve existing process receipt' if File.exist?(receipt)
    log_path = directory + '/' + name + '.log.gz'
    raise 'Preserve existing process log' if File.exist?(log_path)
    record = {status: 'preparing', command: command, cwd: cwd, environment: env,
      started_utc: Time.now.utc.iso8601, exit_code: nil, signal: nil, guard_stop: nil,
      policy: 'Single serial lease; Lean allocation8704MiB; owned RSS<=9GiB; combined worker RSS<two-thirds physicalRAM; actual availableRAM>=1GiB; at most4 Lean workers; bounded2GiB swap credit.',
      owned_rss_cap: 9 * 1024**3, peak_owned_rss: 0, peak_owned_rss_and_swap: 0,
      peak_combined_worker_rss: 0, peak_lean_workers: 0, proof_diagnostic_errors: false}
    save = -> { File.write(receipt, JSON.pretty_generate(record) + "\n") }
    save.call
    pid = nil
    finished = false
    lease = nil
    stream = nil
    begin
      lease = held_lease || File.open(ROOT + '/verification/chevalley/.runner.lock', File::RDWR)
      raise 'Wrong serial lease' unless lease.path == ROOT + '/verification/chevalley/.runner.lock'
      raise 'Another build/audit owns the serial lease' unless lease.flock(File::LOCK_EX | File::LOCK_NB)
      initial = memory
      ceiling = initial.fetch('MemTotal') * 2 / 3
      record[:combined_worker_rss_cap] = ceiling
      if initial.fetch('MemAvailable') < 1024**3 ||
          initial.fetch('MemAvailable') + [initial.fetch('SwapFree'), 2 * 1024**3].min < 2 * 1024**3 ||
          workers.fetch(:combined_rss) + 8704 * 1024**2 >= ceiling
        record[:guard_stop] = 'memory-admission'
        raise 'Memory admission reserve unavailable; preserve this attempt and switch jobs'
      end
      reader, writer = IO.pipe
      pid = Process.spawn(env, *command, chdir: cwd, pgroup: true, out: writer, err: writer)
      writer.close
      record[:pid] = pid
      record[:status] = 'running'
      save.call
      plain = Digest::SHA256.new
      diagnostics = []
      stream = Thread.new do
        Zlib::GzipWriter.open(log_path, Zlib::BEST_SPEED) do |log|
          log.mtime = 0
          reader.each_line do |line|
            log.write(line)
            plain.update(line)
            if line.match?(/\berror(?:\([^\n]*\))?:|PANIC at|declaration uses ['`]sorry['`]/)
              record[:proof_diagnostic_errors] = true
              diagnostics << line.strip if diagnostics.size < 12
            end
          end
        end
        reader.close
      end
      last = Time.now - 30
      loop do
        sample = workers(pid)
        current = memory
        supervisor = File.read('/proc/self/status')
        supervisor_rss = supervisor[/^VmRSS:\s+(\d+)/, 1].to_i * 1024
        supervisor_swap = supervisor[/^VmSwap:\s+(\d+)/, 1].to_i * 1024
        owned_rss = sample[:owned_rss] + supervisor_rss
        record[:peak_owned_rss] = [record[:peak_owned_rss], owned_rss].max
        record[:peak_owned_rss_and_swap] = [record[:peak_owned_rss_and_swap], owned_rss + sample[:owned_swap] + supervisor_swap].max
        record[:peak_combined_worker_rss] = [record[:peak_combined_worker_rss], sample[:combined_rss]].max
        record[:peak_lean_workers] = [record[:peak_lean_workers], sample[:total_lean]].max
        waited = Process.waitpid2(pid, Process::WNOHANG)
        if waited
          finished = true
          record[:exit_code] = waited[1].exitstatus
          record[:signal] = waited[1].termsig
          break
        end
        if owned_rss >= record[:owned_rss_cap] || sample[:combined_rss] >= ceiling ||
            current.fetch('MemAvailable') < 1024**3 || sample[:total_lean] > 4
          record[:guard_stop] = sample[:total_lean] > 4 ? 'worker-ceiling' : 'memory-reserve'
          record[:stop_sample] = {workers: sample, memory: current}
          stop(pid)
          _, result = Process.waitpid2(pid)
          finished = true
          record[:exit_code] = result.exitstatus
          record[:signal] = result.termsig
          break
        end
        if Time.now - last >= 30
          puts JSON.generate(check: name, workers: sample, memory: current)
          $stdout.flush
          last = Time.now
        end
        sleep 1
      end
      stream.value
      record[:log_plain_sha256] = plain.hexdigest
      record[:log_compressed_sha256] = Digest::SHA256.file(log_path).hexdigest
      recovered = Digest::SHA256.new
      Zlib::GzipReader.open(log_path) { |g| recovered.update(g.read(1024**2)) until g.eof? }
      raise 'Compressed process log recovery differs' unless recovered.hexdigest == plain.hexdigest
      record[:log_recovery_verified] = true
      record[:diagnostic_examples] = diagnostics unless diagnostics.empty?
      record[:status] = if record[:guard_stop]
        'memory-stopped'
      elsif record[:exit_code] == 0 && record[:signal].nil? && !record[:proof_diagnostic_errors]
        'process-passed'
      else
        'process-failed'
      end
    rescue StandardError => e
      record[:status] = record[:guard_stop] ? 'memory-stopped' : 'process-failed'
      record[:failure] = e.message
    ensure
      if pid && !finished
        stop(pid)
        Process.waitpid(pid) rescue Errno::ECHILD
      end
      stream&.value
      unless held_lease
        lease&.flock(File::LOCK_UN)
        lease&.close
      end
      record[:finished_utc] = Time.now.utc.iso8601
      record[:final_memory] = memory
      save.call
    end
    record
  end
end
