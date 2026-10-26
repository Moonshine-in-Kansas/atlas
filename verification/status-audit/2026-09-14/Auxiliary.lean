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
  let roots := #[``Atlas.Sporadic.Fischer24.positive_perfect, ``Atlas.Sporadic.Fischer24.card, ``Atlas.Sporadic.Fischer24.positive_index, ``Atlas.Sporadic.Fischer24.positive_faithful, ``Atlas.Sporadic.Fischer24.projection_surjective, ``Atlas.Sporadic.Fischer24.not_simple, ``Atlas.Sporadic.Fischer24.rankThree_action_compatible, ``Atlas.Sporadic.Fischer24.frames_card, ``Atlas.Sporadic.Fischer24.linear_card, ``Atlas.Sporadic.Fischer24.derived, ``Atlas.Sporadic.Fischer24.pentad_frames, ``Atlas.Sporadic.Fischer24.algebra_card, ``Atlas.Sporadic.Fischer24.faithful, ``Atlas.Sporadic.Fischer24.order, ``Atlas.Sporadic.Fischer24.positive_card, ``Atlas.Sporadic.Fischer24.positive_transitive, ``Atlas.Sporadic.Fischer24.rank_three, ``Atlas.Sporadic.Fischer24.pentad_frames_transitive, ``Atlas.Sporadic.Fischer24.finite, ``Atlas.Sporadic.Fischer24.pointwise_frame_kernel, ``Atlas.Sporadic.Fischer24.primitive, ``Atlas.Sporadic.Fischer24.points_card, ``Atlas.Sporadic.Fischer24.pentad_stabilizer, ``Atlas.Sporadic.Fischer24.subdegrees, ``Atlas.Sporadic.Fischer24.no_solvable_normal, ``Atlas.Sporadic.Fischer24.center, ``Atlas.Sporadic.Fischer24.scalar_kernel, ``Atlas.Sporadic.Fischer24.exists_model, ``Atlas.Sporadic.Fischer24.construction, ``Atlas.Sporadic.Fischer24.transitive]
  let h ← IO.FS.Handle.mk "verification/status-audit/2026-09-14/aux-nodes.jsonl" IO.FS.Mode.write
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
