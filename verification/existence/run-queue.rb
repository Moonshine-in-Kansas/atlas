require 'json'
require 'time'
path=ARGV.fetch(0)+'/QUEUE.json'
queue=JSON.parse(File.read(path))
$stdout.sync=true
queue.each do |row|
 next if row['status']=='passed'
 puts "#{Time.now.utc.iso8601}: #{row['target']}"
 row['status']='running'
 File.write(path,JSON.pretty_generate(queue)+"\n")
 ok=system('ruby',File.expand_path('run-entry.rb',__dir__),row.fetch('harness'))
 result_path=row.fetch('harness')+'/RESULT.json'
 result=File.file?(result_path) ? JSON.parse(File.read(result_path)) : {}
 row['status']=ok && result['status']=='passed' ? 'passed' : 'failed'
 row['result']=result_path
 File.write(path,JSON.pretty_generate(queue)+"\n")
 if result['memory_guard_stop']
   warn 'Stopping queue after memory guard; completed results retained.'
   exit 75
 end
end
exit(queue.all?{|r|r['status']=='passed'} ? 0 : 1)
