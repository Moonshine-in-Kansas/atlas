# Owner-authorized swap-aware policy (24 October 2026). Historical guards unchanged.
module DraftMonitor
  GIB = 1024**3
  def self.run(out, name, cwd, env, cmd, stdout: nil)
    m = ChevalleyReplay.memory
    cap = [9*GIB, m.fetch('MemTotal')*2/3-GIB/2].min
    record = {status:'running', command:cmd, started_utc:Time.now.utc.iso8601,
      policy:'Swap-aware: 9 GiB owned RSS+swap cap; combined worker RSS below 2/3 physical RAM; 1 GiB available RAM+free swap reserve; stop on sustained severe pressure.',
      owned_memory_cap:cap}
    path=out+'/'+name+'.json'
    ChevalleyReplay.write(path,record)
    if m.fetch('MemAvailable')+m.fetch('SwapFree') < 2*GIB
      record.merge!(status:'blocked-memory',memory:m)
      ChevalleyReplay.write(path,record)
      return record
    end
    log=out+'/'+name+'.log'
    timed=['/usr/bin/time','-v','-o',out+'/'+name+'.time',*cmd]
    pid=Process.spawn(env,*timed,chdir:cwd,out:stdout || log,err:stdout ? log : [:child,:out],pgroup:true)
    record[:pid]=pid
    ChevalleyReplay.write(path,record)
    puts "#{Time.now.utc.iso8601} #{name} PID=#{pid} log=#{log}"
    status=nil
    guard=nil
    peak=0
    last=Time.now-30
    pressure_since=nil
    begin
      loop do
        done=Process.waitpid2(pid,Process::WNOHANG)
        if done
          status=done.last
          break
        end
        owned=0
        rss=0
        workers=0
        combined=0
        Dir['/proc/[0-9]*/stat'].each do |p|
          begin
            fields=File.read(p).sub(/\A\d+ \(.*\) /,'').split
            s=File.read(p.sub(/stat$/,'status'))
            n=s[/^Name:\s+(\S+)/,1]
            r=s[/^VmRSS:\s+(\d+)/,1].to_i*1024
            combined+=r if %w[codex lean lake ruby lean4export nanoda_bin comparator].include?(n)
            workers+=1 if %w[lean lean4export nanoda_bin comparator].include?(n)
            next unless fields[2].to_i==pid
            rss+=r
            owned+=r+s[/^VmSwap:\s+(\d+)/,1].to_i*1024
          rescue Errno::ENOENT,Errno::ESRCH,Errno::EACCES
            next
          end
        end
        peak=[peak,owned].max
        m=ChevalleyReplay.memory
        psi=File.read('/proc/pressure/memory')[/^full avg10=([\d.]+)/,1].to_f
        severe=psi>25 || m.fetch('MemAvailable')<128*1024**2
        pressure_since=severe ? (pressure_since || Time.now) : nil
        guard='owned RSS+swap cap reached' if owned>=cap
        guard='combined worker RSS ceiling reached' if combined>=m.fetch('MemTotal')*2/3
        guard='combined available RAM and free swap reserve reached' if m.fetch('MemAvailable')+m.fetch('SwapFree')<GIB
        guard='sustained severe memory pressure for 60 seconds' if pressure_since && Time.now-pressure_since>=60
        guard='more than four compute workers' if workers>4
        if guard || Time.now-last>=30
          sample={utc:Time.now.utc.iso8601,stage:name,owned_rss:rss,owned_rss_and_swap:owned,combined_worker_rss:combined,workers:workers,memory:m,psi_full_avg10:psi,guard:guard}
          File.open(out+'/MEMORY.jsonl','a') { |f| f.puts(JSON.generate(sample)) }
          puts "#{name}: owned=#{(owned.to_f/GIB).round(2)} GiB; RAM available=#{(m['MemAvailable'].to_f/GIB).round(2)} GiB; swap free=#{(m['SwapFree'].to_f/GIB).round(2)} GiB; workers=#{workers}"
          last=Time.now
        end
        if guard
          ChevalleyReplay.stop(pid)
          status=Process.waitpid2(pid).last
          break
        end
        sleep 1
      end
    ensure
      ChevalleyReplay.stop(pid) unless status
    end
    record.merge!(status:guard ? 'stopped-resource-guard' : (status.success? ? 'process-passed' : 'failed'),
      finished_utc:Time.now.utc.iso8601,exit_code:status.exitstatus,signal:status.termsig,
      guard_stop:guard,peak_owned_rss_and_swap:peak,final_memory:m,log_sha256:ChevalleyReplay.sha(log))
    ChevalleyReplay.write(path,record)
    puts "#{name}: #{record[:status]}#{guard ? ': '+guard : ''}"
    record
  end
end
