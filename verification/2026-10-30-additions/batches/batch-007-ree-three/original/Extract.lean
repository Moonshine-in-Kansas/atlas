import Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction
import Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure
import Atlas.Comparisons.Exceptional.ReeThree.FieldActionFaithful
import Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget
import Atlas.GroupTheory.SemidirectDerived
import Atlas.LinearGroups.ReeG2.SmallParameter
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Comparisons.ReeThree.Boundary.Coordinates", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.affineVector_coordinates", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.borel_eq_triple", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinateAction", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.coordinateAction_coherence", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinateAction_injective", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinateAction_range", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_root_affine", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_root_none", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_t_affine", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_t_none", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_u_affine", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_u_fixed_iff", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_v_affine", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_w_affine", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_w_none", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinate_w_origin", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.coordinates_card", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.cube_eq", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.generated_eq_four", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.model_generated_by_four", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.oppositeParameters", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.pointRight_root_affine", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.pointRight_w_affine", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.rootModel", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.rootSubgroup_eq_pair", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.root_inv", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.root_mul", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.scalar_cases", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.t", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.tModel", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.t_commutes_v", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.t_conjugate_u", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.t_inv", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.t_order", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.t_square", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.uModel", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.uModel_order", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u_cube", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u_eq_alpha_beta", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u_fourth", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u_inv", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u_ninth", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u_order", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u_sixth", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.u_square", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.unit_cases", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.v", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.vModel", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "definition"), ("Atlas.Comparisons.ReeThree.Boundary.v_conjugate_u", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.v_cube", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.v_eq_beta", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.v_inv", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.v_order", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.v_square", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryRootStructure", "theorem"), ("Atlas.Comparisons.ReeThree.Boundary.wModel", "Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction", "definition"), ("Atlas.Comparisons.ReeThree.fieldAction", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.fieldAction_injective", "Atlas.Comparisons.Exceptional.ReeThree.FieldActionFaithful", "any"), ("Atlas.Comparisons.ReeThree.fieldAut_card", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.frobenius_apply", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.frobenius_order", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.linearFactorEquivDerived", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.linearFactor_card", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.linearFactor_center_trivial", "Atlas.Comparisons.Exceptional.ReeThree.FieldActionFaithful", "any"), ("Atlas.Comparisons.ReeThree.linearFactor_perfect", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.linearFactor_simple", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.projectiveFrobenius_order", "Atlas.Comparisons.Exceptional.ReeThree.FieldActionFaithful", "any"), ("Atlas.Comparisons.ReeThree.scalar_card", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.semilinear_card", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.semilinear_commutator", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.semilinear_derived_card", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.Comparisons.ReeThree.semilinear_derived_simple", "Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget", "any"), ("Atlas.GroupTheory.semidirect_commutator_eq_left", "Atlas.GroupTheory.SemidirectDerived", "any"), ("Atlas.ReeG2.smallParameter_borel_order", "Atlas.LinearGroups.ReeG2.SmallParameter", "any"), ("Atlas.ReeG2.smallParameter_card_condition", "Atlas.LinearGroups.ReeG2.SmallParameter", "any"), ("Atlas.ReeG2.smallParameter_faithful", "Atlas.LinearGroups.ReeG2.SmallParameter", "any"), ("Atlas.ReeG2.smallParameter_order", "Atlas.LinearGroups.ReeG2.SmallParameter", "any"), ("Atlas.ReeG2.smallParameter_point_count", "Atlas.LinearGroups.ReeG2.SmallParameter", "any"), ("Atlas.ReeG2.smallParameter_primitive", "Atlas.LinearGroups.ReeG2.SmallParameter", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "/home/gerald/atlas/claude/release-update-v1.2-20261030/verification-runs/20261030T092950-audit-batch-batch-007-ree-three"
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
