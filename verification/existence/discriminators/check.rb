# Serial preparatory checks, not Comparator or an independent kernel replay.
require 'json'
require 'fileutils'
require 'digest'
require 'time'
lake=ENV.fetch("LAKE",File.join(Dir.home,".elan/bin/lake"))
root=File.expand_path('../../..',__dir__)
Dir.chdir(root)
abort 'Preflight failed' unless system('ruby','verification/existence/discriminators/prepare.rb','--check')
config=JSON.parse(File.read('verification/existence/discriminators/comparator.json'))
names=config.fetch('theorem_names')
out='verification/results/existence-discriminator-precheck-'+Time.now.utc.strftime('%Y%m%dT%H%M%SZ')
FileUtils.mkdir_p(out)
records={}
%w[Challenge Solution].each do |side|
  source=File.read("verification/existence/discriminators/#{side}.lean")
  audit=<<~LEAN

private def canonicalBinders : Lean.Expr → Lean.Expr
  | .forallE _ d b i => .forallE .anonymous (canonicalBinders d) (canonicalBinders b) i
  | .lam _ d b i => .lam .anonymous (canonicalBinders d) (canonicalBinders b) i
  | .letE _ t v b n => .letE .anonymous (canonicalBinders t) (canonicalBinders v) (canonicalBinders b) n
  | .app f a => .app (canonicalBinders f) (canonicalBinders a)
  | .mdata _ e => canonicalBinders e
  | .proj s i e => .proj s i (canonicalBinders e)
  | e => e
open Lean Elab Command in

  run_cmd do
    let names : Array String := #[#{names.map(&:inspect).join(',')}]
    let mut rows : Array Json := #[]
    for name in names do
      let ci ← getConstInfo name.toName
      let ax ← collectAxioms name.toName
      rows := rows.push <| Json.mkObj [("name",toJson name),
        ("type", toJson (reprStr (canonicalBinders ci.type))), ("axioms",toJson (ax.map Name.toString))]
    IO.FS.writeFile #{JSON.generate(out+'/'+side+'.json')} (Json.pretty (toJson rows))
  LEAN
  path=out+'/'+side+'Check.lean'
  File.write(path,"import Lean.Util.CollectAxioms\n"+source+audit)
  start=Process.clock_gettime(Process::CLOCK_MONOTONIC)
  ok=system({'LEAN_NUM_THREADS'=>'1'},lake,'env','lean','-M8192','-j1',path,out:out+'/'+side+'.log',err:[:child,:out])
  abort "#{side} failed; see #{out}/#{side}.log" unless ok
  records[side]={'seconds'=>Process.clock_gettime(Process::CLOCK_MONOTONIC)-start,'rows'=>JSON.parse(File.read(out+'/'+side+'.json'))}
end
c=records.fetch('Challenge').fetch('rows')
s=records.fetch('Solution').fetch('rows')
raise 'Statements differ' unless c.map{|r|[r['name'],r['type']]} == s.map{|r|[r['name'],r['type']]}
raise 'Unapproved solution axiom' unless s.all?{|r|(r['axioms']-config.fetch('permitted_axioms')).empty?}
result={status:'precheck-passed', comparator:'not-run',targets:names.size,
  statement_comparison:'identical compiled expressions after erasing binder names and metadata',
  solution_axioms:s.flat_map{|r|r['axioms']}.uniq.sort,
  reference_placeholders:'deliberate; reference is not a proved result and is not imported by Solution',
  seconds:records.transform_values{|r|r['seconds']},
  files:%w[Challenge.lean Solution.lean comparator.json].to_h{|p|[p,Digest::SHA256.file('verification/existence/discriminators/'+p).hexdigest]},
  source_snapshot:Digest::SHA256.file('verification/2026-09-18/SOURCE_HASHES.json').hexdigest}
File.write(out+'/RESULT.json',JSON.pretty_generate(result)+"\n")
puts "PASS: #{out}/RESULT.json"
