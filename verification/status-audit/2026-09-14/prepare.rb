require 'json'
d='verification/status-audit/2026-09-14'
s=File.read('verification/proof-line-counts/Collect.lean')
roots=s.scan(/``([\w.]+)/).flatten.uniq+%w[Atlas.Sporadic.Fischer24Prime.card Atlas.Sporadic.Fischer24Prime.simple Atlas.Sporadic.Fischer23.card Atlas.Sporadic.Fischer23.simple Atlas.Sporadic.Fischer22.card Atlas.Sporadic.Fischer22.simple]
File.write("#{d}/roots.json",JSON.pretty_generate(roots))
inv=File.readlines("#{d}/inventory.log").filter_map{|l| l.split("ATLAS_DECL\t",2)[1]&.strip&.split("\t")}
props=inv.select{|n,m,k| k=='theorem' && n.match?(/\AAtlas\.(Sporadic\.(Mathieu\d+|Conway[123]|McLaughlin|HigmanSims|Suzuki|Janko2|Fischer22|Fischer23|Fischer24Prime)|Families\.(Cyclic|Alternating))\.[^.]+\z/)}.map(&:first)
selected=(roots+props).uniq
File.write("#{d}/selected.json",JSON.pretty_generate(selected))
File.write("#{d}/Extract.lean", <<~LEAN)
import Atlas
import Lean.DeclarationRange
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[#{selected.map{|n| "``#{n}"}.join(', ')}]
  let h ← IO.FS.Handle.mk "#{d}/nodes.jsonl" IO.FS.Mode.write
  let mut seen : NameSet := {}
  let mut work := roots
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing {n}"
    let deps := ci.getUsedConstantsAsSet.toArray
    work := work ++ deps
    let ty := ci.type.getUsedConstants
    let va := match ci.value? true with
      | some v => v.getUsedConstants
      | none => #[]
    let mod := match env.getModuleIdxFor? n with
      | some idx => env.allImportedModuleNames[idx.toNat]!.toString
      | none => "<kernel>"
    let mut parent := n
    let mut ranges ← findDeclarationRanges? parent
    while ranges.isNone && !parent.isAnonymous do
      parent := parent.getPrefix
      ranges ← findDeclarationRanges? parent
    let span := match ranges with
      | some r => Json.arr #[toJson r.range.pos.line, toJson r.range.endPos.line, toJson r.range.endPos.column]
      | none => Json.null
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let j := Json.mkObj [("name",toJson n.toString),("module",toJson mod),("kind",toJson kind),
      ("type",toJson (ty.map Name.toString)),("value",toJson (va.map Name.toString)),
      ("dependencies",toJson (deps.map Name.toString)),("span",span),("range_parent",toJson parent.toString)]
    h.putStrLn j.compress
  h.flush
  for n in roots do
    logInfo m!"STATEMENT {n}"
    elabCommand (← `(#check @$(mkIdent n)))
    let ax ← collectAxioms n
    logInfo m!"AXIOMS {n}: {ax}"
  logInfo m!"GRAPH COMPLETE {seen.size} declarations; {roots.size} selected roots"
LEAN
