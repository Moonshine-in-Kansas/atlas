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
  let roots := #[``Atlas.finite_psl, ``Atlas.psl_nonabelian_simple, ``Atlas.typeA_construction, ``Atlas.exists_typeA, ``Atlas.typeA_prime_power, ``Atlas.psl_toPGL_injective, ``Atlas.psl_faithful]
  let h ← IO.FS.Handle.mk "verification/status-audit/2026-09-14/extra-nodes.jsonl" IO.FS.Mode.write
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
