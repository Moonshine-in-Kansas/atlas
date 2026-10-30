# Portable, serial, memory-bounded replay of one canonical full checkpoint.
# Run only by the coordinating parent. A validated compiled cache is a prerequisite.
# No downloads, cache creation, historical rewriting or independent-replay claim.
require 'json'
require 'digest'
require 'fileutils'
require 'time'
require 'zlib'
require 'set'
require_relative 'policy'

module AtlasCheckpointReplay
  GIB=1024**3
  ROOT=File.expand_path('..',__dir__)
  class GuardStop < StandardError; end
  def self.write(path, data) = File.write(path,JSON.pretty_generate(data)+"\n")
  def self.sha(path) = Digest::SHA256.file(path).hexdigest
  def self.sources(root)
    (Dir.glob(root+'/Atlas/**/*.lean').map { |p|p.delete_prefix(root+'/') }+
      %w[Atlas.lean lean-toolchain lakefile.toml lake-manifest.json]).sort.to_h { |p|[p,sha(root+'/'+p)] }
  end
  def self.memory
    text=File.read('/proc/meminfo')
    %w[MemTotal MemAvailable].to_h { |key|[key,Integer(text[/^#{key}:\s+(\d+)/,1])*1024] }
  end
  def self.artifacts(root, input_sources)
    input_sources.keys.grep(/\.lean\z/).sort.to_h do |source|
      path='.lake/build/lib/lean/'+source.delete_suffix('.lean')+'.olean'
      parts=path.split('/')
      raise 'Symlinked project cache is not permitted' if parts.each_index.any? { |i|File.symlink?(File.join(root,*parts[0..i])) }
      raise "Missing validated cache artifact #{source}" unless File.file?(root+'/'+path)
      [path,sha(root+'/'+path)]
    end
  end
  def self.owned(pid)
    # The process group includes Lake, Lean and any ordinary child processes.
    rows=Dir.glob('/proc/[0-9]*/stat').filter_map do |path|
      begin
        id=path.split('/')[2].to_i
        stat=File.read(path).sub(/\A\d+ \(.*\) /,'').split
        next unless stat[2].to_i==pid || id==Process.pid
        status=File.read("/proc/#{id}/status")
        [id,status[/^VmRSS:\s+(\d+)/,1].to_i*1024,status[/^VmSwap:\s+(\d+)/,1].to_i*1024,
          status[/^Name:\s+(.*)/,1].to_s]
      rescue Errno::ENOENT, Errno::ESRCH
        nil
      end
    end
    {rss:rows.sum { |r|r[1] },swap:rows.sum { |r|r[2] },workers:rows.count { |r|r[3].match?(/\A(?:lean|lake)(?:$|[- ])/ ) }}
  end
  def self.stop(pid)
    %w[TERM KILL].each do |signal|
      begin
        Process.kill(signal,-pid)
      rescue Errno::ESRCH
        nil
      end
      sleep 0.5 if signal=='TERM'
    end
  end
  def self.run_process(root,out,name,command,diagnostics:true)
    record={status:'started',started_utc:Time.now.utc.iso8601,command:command,
      cwd:root,environment:{LEAN_NUM_THREADS:'2'},allocation_mib:8704,
      rss_cap:9*GIB,available_ram_reserve:GIB,combined_memory_fraction:'2/3',
      peak_owned_rss:0,peak_owned_rss_and_swap:0}
    path=out+'/'+name;pid=nil;finished=false
    begin
      mem=memory
      raise 'Actual RAM admission reserve below 1 GiB' if mem.fetch('MemAvailable')<GIB
      File.open(path+'.log','wb') do |log|
        pid=Process.spawn({'LEAN_NUM_THREADS'=>'2','GIT_OPTIONAL_LOCKS'=>'0'},*command,chdir:root,pgroup:true,out:log,err:[:child,:out])
        record[:pid]=pid
        loop do
          state=owned(pid);mem=memory
          record[:peak_owned_rss]=[record[:peak_owned_rss],state[:rss]].max
          record[:peak_owned_rss_and_swap]=[record[:peak_owned_rss_and_swap],state[:rss]+state[:swap]].max
          reason=if state[:rss]>=9*GIB then '9 GiB aggregate RSS'
          elsif state[:rss]+state[:swap]>=mem['MemTotal']*2/3 then 'two-thirds physical RAM combined worker memory'
          elsif mem['MemAvailable']<GIB then '1 GiB actual available RAM'
          elsif state[:workers]>4 then 'four compute-worker limit'
          end
          File.open(out+'/MEMORY.jsonl','a') { |f|f.puts(JSON.generate({utc:Time.now.utc.iso8601,step:name,**state,**mem})) }
          if reason
            record[:guard_stop]=reason;stop(pid)
          end
          pair=Process.waitpid2(pid,Process::WNOHANG)
          if pair
            status=pair[1];finished=true
            record[:exit_code]=status.exitstatus;record[:signal]=status.termsig
            break
          end
          sleep 0.2
        end
      end
      bad=diagnostics && File.foreach(path+'.log').any? { |line|line.match?(/\berror:|\bPANIC\b|\bsorry\b/) }
      record[:diagnostics_clean]=!bad
      record[:status]=record[:exit_code]==0 && record[:signal].nil? && record[:guard_stop].nil? && !bad ? 'process-passed' : 'process-failed'
    rescue StandardError, Interrupt => e
      record[:status]='process-failed';record[:error]=e.message
      record[:guard_stop]=e.message if e.is_a?(GuardStop)
    ensure
      if pid && !finished
        stop(pid)
        Process.waitpid(pid) rescue Errno::ECHILD
      end
      record[:finished_utc]=Time.now.utc.iso8601
      record[:log_sha256]=sha(path+'.log') if File.file?(path+'.log')
      write(path+'.json',record)
    end
    raise "#{name}: #{record[:error] || record[:guard_stop] || record[:status]}" unless record[:status]=='process-passed'
    path+'.log'
  end
  def self.run(manifest_path,out,root:ROOT)
    root=File.realpath(root);manifest_path=File.realpath(manifest_path);out=File.expand_path(out)
    raise 'Refusing existing output directory' if File.exist?(out)
    raise 'Keep replay output outside sources or under verification/results/' if out.start_with?(root+'/') && !out.start_with?(root+'/verification/results/')
    raise 'Output parent directory must already exist' unless File.directory?(File.dirname(out))
    lease=File.open(ENV.fetch('ATLAS_VERIFICATION_LEASE'),File::RDWR)
    raise 'Another verification owns the single lease' unless lease.flock(File::LOCK_EX|File::LOCK_NB)
    Dir.mkdir(out)
    original=File.binread(manifest_path)
    manifest=JSON.parse(original)
    result={status:'started',mode:'full',checkpoint:manifest.fetch('id'),started_utc:Time.now.utc.iso8601,
      scope:'Complete canonical checkpoint types, definition bodies, type/value dependencies and explicit policies',
      checking:'Fresh extraction against the pinned validated cache; prior normal source proof receipts are separate',
      fresh_project_rebuild:false,independent_replay:false}
    before=sources(root)
    File.binwrite(out+'/CHECKPOINT.json',original)
    write(out+'/SOURCE_HASHES.json',before)
    watcher=nil
    begin
      # Also bound Ruby graph loading/policy evaluation after Lean has exited.
      main=Thread.current
      watcher=Thread.new do
        loop do
          sleep 0.2
          state=owned(-1);mem=memory
          reason=if state[:rss]>=9*GIB then 'Ruby driver reached 9 GiB RSS'
          elsif state[:rss]+state[:swap]>=mem['MemTotal']*2/3 then 'Ruby driver reached two-thirds RAM'
          elsif mem['MemAvailable']<GIB then 'Actual available RAM below 1 GiB'
          end
          if reason
            main.raise(GuardStop,reason)
            break
          end
        end
      rescue StandardError=>e
        main.raise(GuardStop,"Memory monitor failed: #{e.message}")
      end
      raise 'Full mode with definitions=true required' unless manifest['mode']=='full' && manifest['definitions']==true
      raise 'Unapproved axioms' unless manifest.fetch('allowed_axioms').sort==AtlasVerification::AXIOMS.sort
      imports=manifest.fetch('imports');targets=manifest.fetch('targets')
      raise 'Empty imports/targets' if imports.empty? || targets.empty?
      raise 'Noncanonical imports' unless imports.all? { |n|n.match?(/\AAtlas(?:\.[A-Za-z0-9_]+)*\z/) }
      raise 'Duplicate targets' unless targets.map { |r|r.fetch('declaration') }.uniq.size==targets.size
      targets.each do |r|
        raise 'Invalid target module/kind' unless r.fetch('module').match?(/\AAtlas(?:\.[A-Za-z0-9_]+)*\z/) && %w[any theorem definition].include?(r.fetch('kind'))
      end
      result[:targets]=targets.size;write(out+'/roots.json',targets)
      cache_before=artifacts(root,before)
      write(out+'/CACHE_ARTIFACTS.json',cache_before)
      tool_paths=%w[verification/replay_checkpoint.rb verification/Extract.lean.in verification/policy.rb]
      tools=tool_paths.to_h { |p|[p,sha(root+'/'+p)] }
      write(out+'/TOOLS.json',tools)
      lake=ENV.fetch('LAKE','lake')
      packages=JSON.parse(File.read(root+'/lake-manifest.json')).fetch('packages')
      verify_packages=lambda do |phase|
        packages.to_h do |pkg|
          raise 'Unpinned package' unless pkg['type']=='git' && pkg.fetch('name').match?(/\A[A-Za-z0-9_-]+\z/) && pkg.fetch('rev').match?(/\A[0-9a-f]{40}\z/)
          path=root+'/.lake/packages/'+pkg['name']
          raise 'Missing pinned package; no network fallback' unless File.directory?(path)
          rev=File.read(run_process(root,out,phase+'-'+pkg['name']+'-revision',['git','-C',path,'rev-parse','HEAD'])).strip
          dirty=File.read(run_process(root,out,phase+'-'+pkg['name']+'-status',['git','-C',path,'status','--porcelain=v1','--untracked-files=no'])).strip
          raise 'Dirty or wrong package revision' unless rev==pkg['rev'] && dirty.empty?
          [pkg['name'],rev]
        end
      end
      result[:dependency_revisions]=verify_packages.call('before')
      version=File.read(run_process(root,out,'lean-version',[lake,'env','lean','--version']))
      pin=File.read(root+'/lean-toolchain').strip.split(':').last.delete_prefix('v')
      raise 'Wrong Lean version' unless version.match?(/\bversion #{Regexp.escape(pin)}(?:\s|,|\))/)
      result[:lean_version]=version.strip
      template=File.read(root+'/verification/Extract.lean.in')
      values={'@@IMPORTS@@'=>imports.map { |n|'import '+n }.join("\n"),
        '@@TARGETS@@'=>'#['+targets.map { |r|'('+r.values_at('declaration','module','kind').map { |s|JSON.generate(s) }.join(', ')+')' }.join(', ')+']',
        '@@OUTPUT@@'=>JSON.generate(out),'@@FULL@@'=>'true','@@DEFINITIONS@@'=>'true'}
      values.each { |key,value|template=template.gsub(key) { value } }
      raise 'Unexpanded extractor template' if template.match?(/@@[A-Z_]+@@/)
      File.write(out+'/Extract.lean',template)
      log_path=run_process(root,out,'full-dependency-extraction',[lake,'env','lean','-j2','-M8704',
        '-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-Dweak.linter.mathlibStandardSet=true',
        '-DmaxSynthPendingDepth=3','--root='+root,out+'/Extract.lean'])
      raise 'Incomplete extraction' unless File.foreach(log_path).any? { |l|l.strip=="SHARED EXTRACTION COMPLETE: #{targets.size} targets" }
      declarations=File.readlines(out+'/declarations.jsonl').map { |line|JSON.parse(line) }
      raise 'Incomplete compiled selection' unless declarations.map { |r|r.fetch('declaration') }.sort==targets.map { |r|r['declaration'] }.sort
      nodes={}
      File.foreach(out+'/dependencies.jsonl') do |line|
        node=JSON.parse(line);name=node.fetch('name')
        raise 'Duplicate dependency node' if nodes.key?(name)
        nodes[name]=node
      end
      result[:boundaries]=AtlasVerification.check_policy(manifest,declarations,nodes)
      write(out+'/POLICY_RESULTS.json',{manifest.fetch('id')=>{status:'passed',
        manifest_sha256:Digest::SHA256.hexdigest(original),targets:targets.size,
        dependency_nodes:nodes.size,boundaries:result[:boundaries]}})
      raise 'Package changed during replay' unless result[:dependency_revisions]==verify_packages.call('after')
      raise 'Source or pins changed during replay' unless before==sources(root)
      raise 'Manifest changed during replay' unless File.binread(manifest_path)==original
      raise 'Audit tool changed during replay' unless tools.all? { |p,h|sha(root+'/'+p)==h }
      cache_after=artifacts(root,before);write(out+'/CACHE_ARTIFACTS_AFTER.json',cache_after)
      raise 'Validated project cache changed during replay' unless cache_after==cache_before
      result.merge!(status:'passed',sources_unchanged:true,cache_artifacts_unchanged:true,
        dependency_nodes:nodes.size,axioms:declarations.flat_map { |r|r.fetch('axioms') }.uniq.sort)
    rescue StandardError, Interrupt => e
      result.merge!(status:'incomplete',error:e.message)
      result[:guard_stop]=e.message if e.is_a?(GuardStop)
    ensure
      watcher&.kill;watcher&.join
      result[:finished_utc]=Time.now.utc.iso8601
      begin
        write(out+'/SOURCE_HASHES_AFTER.json',sources(root))
      rescue StandardError=>e
        result.merge!(status:'incomplete',finalization_error:e.message)
      end
      write(out+'/RESULT.json',result)
      uncompressed={}
      %w[full-dependency-extraction.log dependencies.jsonl].each do |name|
        next unless File.file?(out+'/'+name)
        uncompressed[name]=sha(out+'/'+name)
        Zlib::GzipWriter.open(out+'/'+name+'.gz') { |g|g.mtime=0;File.open(out+'/'+name,'rb') { |f|IO.copy_stream(f,g) } }
      end
      artifacts=Dir.glob(out+'/**/*').select { |p|File.file?(p) }.sort.to_h { |p|[p.delete_prefix(out+'/'),sha(p)] }
      write(out+'/BUNDLE.json',{format:1,files:artifacts,uncompressed_hashes:uncompressed})
      lease.flock(File::LOCK_UN);lease.close
    end
    puts JSON.generate(result)
    result[:status]=='passed' ? 0 : 1
  end
end
if $PROGRAM_NAME==__FILE__
  begin
    raise 'Usage: ruby verification/replay_checkpoint.rb MANIFEST NEW_OUTPUT_DIRECTORY' unless ARGV.size==2
    exit AtlasCheckpointReplay.run(*ARGV)
  rescue StandardError=>e
    warn "Checkpoint replay refused: #{e.message}"
    exit 1
  end
end
