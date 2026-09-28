# Runs the real pinned Comparator; records raw evidence without promoting it.
require 'json'
require 'digest'
require 'time'
require 'open3'
root=File.expand_path('../..',__dir__)
harness=ARGV.fetch(0)
abort 'Unexpected harness' unless harness.start_with?(root+'/verification/results/existence-contract-') && File.directory?(harness)
abort 'Refusing to overwrite an existing run' if File.exist?(harness+'/RESULT.json')
$stdout.sync=true
Dir.chdir(harness)
files=%w[Challenge.lean Solution.lean comparator.json lean-toolchain lakefile.toml lake-manifest.json]
sha=->(p){Digest::SHA256.file(p).hexdigest}
source_paths=Dir.glob(root+'/Atlas/**/*.lean')+[root+'/Atlas.lean',root+'/lean-toolchain',root+'/lakefile.toml',root+'/lake-manifest.json']
source_hashes=source_paths.sort.to_h{|p|[p.delete_prefix(root+'/'),sha.call(p)]}
File.write('SOURCE_HASHES.json',JSON.pretty_generate(source_hashes)+"\n")
comparator_root=ENV.fetch('COMPARATOR_ROOT')
exporter_root=ENV.fetch('EXPORTER_ROOT')
landrun_root=ENV.fetch('LANDRUN_ROOT')
bins={'comparator'=>comparator_root+'/.lake/build/bin/comparator',
      'lean4export'=>exporter_root+'/.lake/build/bin/lean4export',
      'landrun'=>landrun_root+'/landrun'}
versions={'comparator'=>[comparator_root,'2312244ac716564a61cc0bf4e107d9abf1757a61'],
          'lean4export'=>[exporter_root,'cacf989bd75f608700820f6afc595f32e7a99a4d'],
          'landrun'=>[landrun_root,'811cfff51ceaf3d9843708aa6d22e9b84ccac8b4']}
versions.each do |name,(dir,rev)|
 actual,status=Open3.capture2('git','-C',dir,'rev-parse','HEAD')
 abort "Wrong #{name} revision" unless status.success? && actual.strip==rev
 diff,status=Open3.capture2('git','-C',dir,'diff','--name-only','HEAD')
 abort "Modified #{name} sources" unless status.success? && diff.empty?
end
before=files.to_h{|p|[p,sha.call(p)]}
record={status:'running',started_utc:Time.now.utc.iso8601,targets:JSON.parse(File.read('comparator.json')).fetch('theorem_names').size,files:before,tools:versions.transform_values{|v|v[1]},binaries:bins.transform_values{|p|sha.call(p)},axioms:%w[propext Quot.sound Classical.choice],reference:'mathlib-only existence statements; not construction recognition',memory_guard:'combined checker/worker RSS below 9 GiB and 256 MiB available reserve; one driver'}
File.write('RESULT.json',JSON.pretty_generate(record)+"\n")
env={'LEAN_NUM_THREADS'=>'1','PATH'=>[File.dirname(bins['landrun']),File.dirname(bins['lean4export']),File.dirname(ENV.fetch('LAKE',File.join(Dir.home,'.elan/bin/lake'))),ENV['PATH']].join(':')}
cmd=['/usr/bin/time','-v','-o','time.txt',ENV.fetch('LAKE',File.join(Dir.home,'.elan/bin/lake')),'env',bins['comparator'],'comparator.json']
pid=Process.spawn(env,*cmd,out:'comparator.log',err:[:child,:out],pgroup:true)
puts "Comparator PID=#{pid}; output=#{harness}/comparator.log"
limit=[9*1024**3,File.read('/proc/meminfo')[/^MemTotal:\s+(\d+)/,1].to_i*1024*2/3].min
peak=0
status=nil
guard=nil
last=Time.now-30
loop do
 done=Process.waitpid2(pid,Process::WNOHANG)
 if done
   status=done[1];break
 end
 rss=Dir.glob('/proc/[0-9]*/status').sum do |p|
  begin
   s=File.read(p)
   %w[codex lean lake ruby comparator lean4export].include?(s[/^Name:\s+(\S+)/,1]) ? s[/^VmRSS:\s+(\d+)/,1].to_i*1024 : 0
  rescue Errno::ENOENT,Errno::EACCES,Errno::ESRCH
   0
  end
 end
 peak=[peak,rss].max
 avail=File.read('/proc/meminfo')[/^MemAvailable:\s+(\d+)/,1].to_i*1024
 if rss>=limit || avail<256*1024**2
  guard=rss>=limit ? '9 GiB combined RSS ceiling reached' : '256 MiB available-memory reserve reached'
  Process.kill('TERM',-pid) rescue nil
  sleep 2
  Process.kill('KILL',-pid) rescue nil
  _,status=Process.waitpid2(pid)
  break
 end
 if Time.now-last>=30
  puts "#{Time.now.utc.iso8601} combined RSS=#{rss}; available=#{avail}"
  last=Time.now
 end
 sleep 2
end
log=File.read('comparator.log')
unchanged=files.all?{|p|sha.call(p)==before[p]} && source_paths.all?{|p|sha.call(p)==source_hashes[p.delete_prefix(root+'/')]}
passed=status.success? && guard.nil? && unchanged && log.include?('Your solution is okay!') && log.include?('Lean default kernel accepts the solution')
record.merge!(status:passed ? 'passed' : 'failed',finished_utc:Time.now.utc.iso8601,exit_code:status.exitstatus,signal:status.termsig,memory_guard_stop:guard,peak_combined_rss:peak,inputs_unchanged:unchanged,log_sha256:sha.call('comparator.log'))
File.write('RESULT.json',JSON.pretty_generate(record)+"\n")
puts "#{record[:status]}: #{harness}/RESULT.json"
exit(passed ? 0 : 1)
