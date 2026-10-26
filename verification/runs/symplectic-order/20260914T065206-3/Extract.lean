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
  let rootSpecs : Array (String × String × String) := #[("Atlas.LinearFunctional.card_fiber", "Atlas.LinearAlgebra.LinearFunctionalFiber", "theorem"), ("Atlas.LinearFunctional.fiberEquivKernel", "Atlas.LinearAlgebra.LinearFunctionalFiber", "definition"), ("Atlas.Symplectic.HyperbolicPairs", "Atlas.LinearGroups.Symplectic.PairCount", "definition"), ("Atlas.Symplectic.ScalarKernel", "Atlas.LinearGroups.Symplectic.Center", "definition"), ("Atlas.Symplectic.card_center", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.card_psp", "Atlas.LinearGroups.Symplectic.ProjectiveOrder", "theorem"), ("Atlas.Symplectic.card_psp_mul_center", "Atlas.LinearGroups.Symplectic.ProjectiveOrder", "theorem"), ("Atlas.Symplectic.card_sp", "Atlas.LinearGroups.Symplectic.Order", "theorem"), ("Atlas.Symplectic.card_sp_succ", "Atlas.LinearGroups.Symplectic.PairAction", "theorem"), ("Atlas.Symplectic.centerEquivScalarKernel", "Atlas.LinearGroups.Symplectic.Center", "definition"), ("Atlas.Symplectic.center_denominator_positive", "Atlas.LinearGroups.Symplectic.OrderInterface", "theorem"), ("Atlas.Symplectic.center_mul_card_psp", "Atlas.LinearGroups.Symplectic.OrderInterface", "theorem"), ("Atlas.Symplectic.center_order_dvd", "Atlas.LinearGroups.Symplectic.ProjectiveOrder", "theorem"), ("Atlas.Symplectic.central_is_scalar", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.central_preserves_lines", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.exists_pair_transporter", "Atlas.LinearGroups.Symplectic.PairAction", "theorem"), ("Atlas.Symplectic.extendLinear", "Atlas.LinearGroups.Symplectic.PairStabilizer", "definition"), ("Atlas.Symplectic.extendLinear_headTail", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.extendLinear_preserves", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.extendPair", "Atlas.LinearGroups.Symplectic.PairStabilizer", "definition"), ("Atlas.Symplectic.extend_restrict", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.headTail_decomposition", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.headTail_e", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.headTail_f", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.hyperbolicPairs_card", "Atlas.LinearGroups.Symplectic.PairCount", "theorem"), ("Atlas.Symplectic.mem_center_iff_scalar", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.mem_pairStabilizer", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.nonzero_vector_card", "Atlas.LinearGroups.Symplectic.PairCount", "theorem"), ("Atlas.Symplectic.orderNumerator_succ", "Atlas.LinearGroups.Symplectic.Order", "theorem"), ("Atlas.Symplectic.pairFiberEquiv", "Atlas.LinearGroups.Symplectic.PairCount", "definition"), ("Atlas.Symplectic.pairStabilizer", "Atlas.LinearGroups.Symplectic.PairStabilizer", "definition"), ("Atlas.Symplectic.pairStabilizerEquiv", "Atlas.LinearGroups.Symplectic.PairStabilizer", "definition"), ("Atlas.Symplectic.pairStabilizer_block", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.pairStabilizer_head", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.pairStabilizer_tail", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.partner_card", "Atlas.LinearGroups.Symplectic.PairCount", "theorem"), ("Atlas.Symplectic.restrictPair", "Atlas.LinearGroups.Symplectic.PairStabilizer", "definition"), ("Atlas.Symplectic.restrictPair_apply", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.restrict_extend", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.scalarElement", "Atlas.LinearGroups.Symplectic.Center", "definition"), ("Atlas.Symplectic.scalarElement_apply", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.scalarKernel_square", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.scalarToCenter", "Atlas.LinearGroups.Symplectic.Center", "definition"), ("Atlas.Symplectic.scalarToCenter_injective", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.scalarToCenter_surjective", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.scalar_is_central", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.scalar_square_eq_one", "Atlas.LinearGroups.Symplectic.Center", "theorem"), ("Atlas.Symplectic.standardPair", "Atlas.LinearGroups.Symplectic.PairAction", "definition"), ("Atlas.Symplectic.standardPairOrbitEquiv", "Atlas.LinearGroups.Symplectic.PairAction", "definition"), ("Atlas.Symplectic.standardPair_stabilizer", "Atlas.LinearGroups.Symplectic.PairAction", "theorem"), ("Atlas.Symplectic.tailLinear", "Atlas.LinearGroups.Symplectic.PairStabilizer", "definition"), ("Atlas.Symplectic.tailLinear_preserves", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.tailMap", "Atlas.LinearGroups.Symplectic.PairStabilizer", "definition"), ("Atlas.Symplectic.tailMap_apply", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.tailMap_mul", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.tailMap_one", "Atlas.LinearGroups.Symplectic.PairStabilizer", "theorem"), ("Atlas.Symplectic.vector_finrank", "Atlas.LinearGroups.Symplectic.PairCount", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/symplectic-order/20260914T065206-3"
  let full : Bool := true
  let printDefinitions : Bool := true
  let reports ← IO.FS.Handle.mk (outDir ++ "/declarations.jsonl") IO.FS.Mode.write
  for (name, expectedModule, kind) in rootSpecs do
    let n := name.toName
    let some ci := env.find? n | throwError "Missing compiled declaration {n}"
    let mod : String := match env.getModuleIdxFor? n with
      | some idx => env.allImportedModuleNames[idx.toNat]!.toString
      | none => "<kernel>"
    unless expectedModule.isEmpty || expectedModule == mod do
      throwError "Wrong source module for {n}: {mod}"
    if kind == "theorem" && !ci.isTheorem then throwError "Not a theorem: {n}"
    if kind == "definition" && ci.isTheorem then throwError "Unexpected theorem: {n}"
    let ax ← collectAxioms n
    reports.putStrLn (Json.mkObj [("declaration",toJson name),("module",toJson mod),
      ("theorem",toJson ci.isTheorem),("axioms",toJson (ax.map Name.toString))]).compress
    if full then
      logInfo m!"STATEMENT {n} SOURCE {mod}"
      elabCommand (← `(#check @$(mkIdent n)))
  reports.flush
  if full then
    let graph ← IO.FS.Handle.mk (outDir ++ "/dependencies.jsonl") IO.FS.Mode.write
    let mut seen : NameSet := {}
    let mut work := roots
    while !work.isEmpty do
      let n := work.back!
      work := work.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throwError "Missing dependency {n}"
      let deps := ci.getUsedConstantsAsSet.toArray
      work := work ++ deps
      let mod : String := match env.getModuleIdxFor? n with
        | some idx => env.allImportedModuleNames[idx.toNat]!.toString
        | none => "<kernel>"
      let mut parent := n
      let mut ranges ← findDeclarationRanges? parent
      while ranges.isNone && !parent.isAnonymous do
        parent := parent.getPrefix
        ranges ← findDeclarationRanges? parent
      let sourceMod : String := match env.getModuleIdxFor? parent with
        | some idx => env.allImportedModuleNames[idx.toNat]!.toString
        | none => "<unavailable>"
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
      let valueDeps := match ci.value? true with
        | some v => v.getUsedConstants
        | none => #[]
      graph.putStrLn (Json.mkObj [("name",toJson n.toString),("module",toJson mod),
        ("kind",toJson kind),("dependencies",toJson (deps.map Name.toString)),
        ("type",toJson (ci.type.getUsedConstants.map Name.toString)),
        ("value",toJson (valueDeps.map Name.toString)),("span",span),
        ("range_parent",toJson parent.toString),("source_module",toJson sourceMod)]).compress
    graph.flush
  if printDefinitions then
    let mut seen : NameSet := {}
    let mut work := roots
    while !work.isEmpty do
      let n := work.back!
      work := work.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throwError "Missing definition {n}"
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.allImportedModuleNames[idx.toNat]!.toString
      unless mod.startsWith "Atlas." do continue
      work := work ++ ci.type.getUsedConstants
      unless ci.isTheorem do
        logInfo m!"DEFINITION {n} SOURCE {mod}"
        elabCommand (← `(#print $(mkIdent n)))
        if let some v := ci.value? true then work := work ++ v.getUsedConstants
  logInfo m!"SHARED EXTRACTION COMPLETE: {roots.size} targets"
