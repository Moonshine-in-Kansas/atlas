require 'json'
d='verification/status-audit/2026-09-14'
roots=JSON.parse(File.read("#{d}/selected.json"))
extra=%w[Atlas.finite_psl Atlas.psl_nonabelian_simple Atlas.typeA_construction Atlas.exists_typeA Atlas.typeA_prime_power Atlas.psl_toPGL_injective Atlas.psl_faithful]
File.write("#{d}/extra.json",JSON.pretty_generate(extra))
File.write("#{d}/Definitions.lean", <<~LEAN)
import Atlas
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
  let roots := #[#{(roots+extra).map{|n| "``#{n}"}.join(', ')}]
  let mut seen : NameSet := {}
  let mut work := roots
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing {n}"
    let mod : String := match env.getModuleIdxFor? n with
      | some idx => env.allImportedModuleNames[idx.toNat]!.toString
      | none => "<kernel>"
    unless mod.startsWith "Atlas." do continue
    work := work ++ ci.type.getUsedConstants
    if ci.isTheorem then
      if roots.contains n then
        logInfo m!"STATEMENT {n} SOURCE {mod}"
        elabCommand (← `(#check @$(mkIdent n)))
    else
      logInfo m!"DEFINITION {n} SOURCE {mod}"
      elabCommand (← `(#print $(mkIdent n)))
      if let some v := ci.value? true then work := work ++ v.getUsedConstants
#print Group
#print DivInvMonoid
#print Monoid
#print Semigroup
#print MulOneClass
#print Inv
#print Div
#print Mul
#print One
#print Nat.card
#print Cardinal.toNat
#print IsSimpleGroup
#print Nontrivial
#print Subgroup
#print Subgroup.Normal
#print IsMulCommutative
#print propext
#print Classical.choice
#print Quot.sound
#synth Group Atlas.Sporadic.Fischer22.Model
#synth Finite Atlas.Sporadic.Fischer22.Model
#synth Group (Atlas.Families.Cyclic.Model 5)
#print Atlas.Sporadic.Fischer22.Model
#print Atlas.Families.Cyclic.Model
LEAN
