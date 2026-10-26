import Atlas.GroupTheory.PrimitivePointChains
import Atlas.GroupTheory.PrimitivePointChainTransport
import Atlas.LinearGroups.F4.CommonOpposite
import Atlas.LinearGroups.F4.GeometryOneStepObstruction
import Atlas.LinearGroups.F4.OppositePointOrbit
import Atlas.LinearGroups.F4.PointOpposition
import Atlas.LinearGroups.F4.NearPointGeometry
import Atlas.LinearGroups.F4.NearDetection
import Atlas.LinearGroups.F4.CanonicalNearEscape
import Atlas.LinearGroups.F4.NearSpinRootMaps
import Atlas.LinearGroups.F4.NearSpinReduction
import Atlas.LinearGroups.F4.NearPointReduction
import Atlas.LinearGroups.F4.NearPointEscape
import Atlas.Algebra.Albert.ShortRootPairing
import Atlas.LinearGroups.F4.ParabolicPairingEscape
import Atlas.LinearGroups.F4.NonNearPointEscape
import Atlas.LinearGroups.F4.PointPrimitivityCriterion
import Atlas.LinearGroups.F4.PointPrimitivity
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Albert.tracePairing_self", "Atlas.Algebra.Albert.ShortRootPairing", "theorem"), ("Atlas.Albert.tracePairing_shortRootLinear", "Atlas.Algebra.Albert.ShortRootPairing", "theorem"), ("Atlas.Albert.tracePairing_shortRootLinear_one_ne_zero", "Atlas.Algebra.Albert.ShortRootPairing", "theorem"), ("Atlas.Albert.tracePairing_shortRootLinear_white", "Atlas.Algebra.Albert.ShortRootPairing", "theorem"), ("Atlas.F4.PointsOpposite", "Atlas.LinearGroups.F4.PointOpposition", "any"), ("Atlas.F4.action_rep_scale", "Atlas.LinearGroups.F4.PointOpposition", "theorem"), ("Atlas.F4.baseVector_mem_parabolicImageZero", "Atlas.LinearGroups.F4.GeometryOneStepObstruction", "theorem"), ("Atlas.F4.baseVector_ne_smul_parabolicVector", "Atlas.LinearGroups.F4.GeometryOneStepObstruction", "theorem"), ("Atlas.F4.canonicalNearFirst", "Atlas.LinearGroups.F4.CanonicalNearEscape", "any"), ("Atlas.F4.canonicalNearFirst_A0", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearFirst_fixes_C0", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearFirst_fixes_point", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearFirst_mem_rootGenerated", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearIntermediate", "Atlas.LinearGroups.F4.CanonicalNearEscape", "any"), ("Atlas.F4.canonicalNearOpposite", "Atlas.LinearGroups.F4.CanonicalNearEscape", "any"), ("Atlas.F4.canonicalNearOpposite_chain", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearOpposite_pairing", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearOpposite_projective", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearSecond", "Atlas.LinearGroups.F4.CanonicalNearEscape", "any"), ("Atlas.F4.canonicalNearSecond_B4", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearSecond_fixes_A0", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearSecond_fixes_point", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonicalNearSecond_mem_rootGenerated", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.canonical_near_stabilizer_chain_escape", "Atlas.LinearGroups.F4.CanonicalNearEscape", "theorem"), ("Atlas.F4.halfRoot_near_axis", "Atlas.LinearGroups.F4.NearPointReduction", "theorem"), ("Atlas.F4.imageZero_rankOne_iff", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.mem_near_of_nonNearCoordinates_zero", "Atlas.LinearGroups.F4.NearDetection", "theorem"), ("Atlas.F4.nearAfterThree", "Atlas.LinearGroups.F4.NearSpinReduction", "any"), ("Atlas.F4.nearClearedSpin", "Atlas.LinearGroups.F4.NearSpinReduction", "any"), ("Atlas.F4.nearClearedSpin_eq", "Atlas.LinearGroups.F4.NearSpinReduction", "theorem"), ("Atlas.F4.nearClearingWord", "Atlas.LinearGroups.F4.NearSpinReduction", "any"), ("Atlas.F4.nearClearingWord_apply", "Atlas.LinearGroups.F4.NearSpinReduction", "theorem"), ("Atlas.F4.nearDualCoordinate", "Atlas.LinearGroups.F4.NearPointReduction", "any"), ("Atlas.F4.nearHyperbolicEquiv", "Atlas.LinearGroups.F4.NearPointGeometry", "any"), ("Atlas.F4.nearImageChart", "Atlas.LinearGroups.F4.NearPointGeometry", "any"), ("Atlas.F4.nearPivot", "Atlas.LinearGroups.F4.NearPointReduction", "any"), ("Atlas.F4.nearPivotWord", "Atlas.LinearGroups.F4.NearPointReduction", "any"), ("Atlas.F4.nearPivot_dual_destination", "Atlas.LinearGroups.F4.NearPointReduction", "theorem"), ("Atlas.F4.nearPivot_nonzero_coordinate", "Atlas.LinearGroups.F4.NearPointReduction", "theorem"), ("Atlas.F4.nearPoint_parabolic_to_base", "Atlas.LinearGroups.F4.NearPointEscape", "theorem"), ("Atlas.F4.nearPoint_stabilizer_chain_escape", "Atlas.LinearGroups.F4.NearPointEscape", "theorem"), ("Atlas.F4.nearQuadratic", "Atlas.LinearGroups.F4.NearPointGeometry", "any"), ("Atlas.F4.nearQuadratic_hyperbolic", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.nearSpinCoordinates", "Atlas.LinearGroups.F4.NearPointGeometry", "any"), ("Atlas.F4.nearStep", "Atlas.LinearGroups.F4.NearSpinRootMaps", "any"), ("Atlas.F4.nearStepSpin", "Atlas.LinearGroups.F4.NearSpinRootMaps", "any"), ("Atlas.F4.nearStep_apply", "Atlas.LinearGroups.F4.NearSpinRootMaps", "theorem"), ("Atlas.F4.nearVector", "Atlas.LinearGroups.F4.NearPointGeometry", "any"), ("Atlas.F4.nearVector_C0", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.nearVector_adjoint", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.nearVector_mem_imageZero", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.nearVector_pairing_dual", "Atlas.LinearGroups.F4.NearPointReduction", "theorem"), ("Atlas.F4.nearVector_parabolic_reduce", "Atlas.LinearGroups.F4.NearPointReduction", "theorem"), ("Atlas.F4.nearVector_rankOne_iff", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.nearVector_reconstruction", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.nearVector_reduce_pivot", "Atlas.LinearGroups.F4.NearSpinReduction", "theorem"), ("Atlas.F4.nearVector_spin", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.nearVector_trace", "Atlas.LinearGroups.F4.NearPointGeometry", "theorem"), ("Atlas.F4.no_one_step_opposite_move_at_parabolicPoint", "Atlas.LinearGroups.F4.GeometryOneStepObstruction", "theorem"), ("Atlas.F4.nonNearCoordinates", "Atlas.LinearGroups.F4.NearDetection", "any"), ("Atlas.F4.nonNearDetectingRoot", "Atlas.LinearGroups.F4.ParabolicPairingEscape", "any"), ("Atlas.F4.nonNearDetectingRoot_parabolic", "Atlas.LinearGroups.F4.ParabolicPairingEscape", "theorem"), ("Atlas.F4.nonnear_parabolic_self_pairing", "Atlas.LinearGroups.F4.ParabolicPairingEscape", "theorem"), ("Atlas.F4.nonnear_point_parabolic_move", "Atlas.LinearGroups.F4.NonNearPointEscape", "theorem"), ("Atlas.F4.nonnear_point_stabilizer_chain_escape", "Atlas.LinearGroups.F4.NonNearPointEscape", "theorem"), ("Atlas.F4.normalizeOppositeVector", "Atlas.LinearGroups.F4.OppositePointOrbit", "any"), ("Atlas.F4.oppositeCell_pairing_detects_offDiagonal", "Atlas.LinearGroups.F4.CommonOpposite", "theorem"), ("Atlas.F4.opposite_points_parabolic_transitive", "Atlas.LinearGroups.F4.OppositePointOrbit", "theorem"), ("Atlas.F4.opposite_points_parabolic_transitive_pairing", "Atlas.LinearGroups.F4.OppositePointOrbit", "theorem"), ("Atlas.F4.opposite_points_stabilizer_transitive", "Atlas.LinearGroups.F4.PointOpposition", "theorem"), ("Atlas.F4.opposite_vectors_parabolic_transport", "Atlas.LinearGroups.F4.OppositePointOrbit", "theorem"), ("Atlas.F4.parabolicImageZero_tracePairing", "Atlas.LinearGroups.F4.GeometryOneStepObstruction", "theorem"), ("Atlas.F4.parabolicStabilizer_baseVector_pairing_zero", "Atlas.LinearGroups.F4.GeometryOneStepObstruction", "theorem"), ("Atlas.F4.parabolic_detecting_move", "Atlas.LinearGroups.F4.ParabolicPairingEscape", "theorem"), ("Atlas.F4.point_eq_parabolic_of_nearSpin_zero", "Atlas.LinearGroups.F4.NearPointEscape", "theorem"), ("Atlas.F4.pointsOpposite_common", "Atlas.LinearGroups.F4.PointOpposition", "theorem"), ("Atlas.F4.pointsOpposite_parabolic_iff", "Atlas.LinearGroups.F4.PointOpposition", "theorem"), ("Atlas.F4.pointsOpposite_smul_iff", "Atlas.LinearGroups.F4.PointOpposition", "theorem"), ("Atlas.F4.pointsOpposite_symm", "Atlas.LinearGroups.F4.PointOpposition", "theorem"), ("Atlas.F4.tracePairing_shortRoot", "Atlas.LinearGroups.F4.ParabolicPairingEscape", "theorem"), ("Atlas.F4.whiteZeroPoints_common_opposite", "Atlas.LinearGroups.F4.OppositePointOrbit", "theorem"), ("Atlas.F4.whiteZeroPoints_primitive", "Atlas.LinearGroups.F4.PointPrimitivity", "theorem"), ("Atlas.F4.whiteZeroPoints_primitive_of_base_escape", "Atlas.LinearGroups.F4.PointPrimitivityCriterion", "theorem"), ("Atlas.F4.whiteZero_common_opposite", "Atlas.LinearGroups.F4.CommonOpposite", "theorem"), ("Atlas.F4.whiteZero_vectors_common_opposite", "Atlas.LinearGroups.F4.OppositePointOrbit", "theorem"), ("Atlas.GroupTheory.primitive_of_nonrelated_orbit_and_chains", "Atlas.GroupTheory.PrimitivePointChains", "theorem"), ("Atlas.GroupTheory.stabilizerMoveChain_escape_smul", "Atlas.GroupTheory.PrimitivePointChainTransport", "theorem"), ("Atlas.GroupTheory.stabilizerMoveChain_mem_block", "Atlas.GroupTheory.PrimitivePointChains", "theorem"), ("Atlas.GroupTheory.stabilizerMoveChain_smul", "Atlas.GroupTheory.PrimitivePointChainTransport", "theorem"), ("Atlas.GroupTheory.stabilizerMoveChain_smul_iff", "Atlas.GroupTheory.PrimitivePointChainTransport", "theorem"), ("Atlas.GroupTheory.stabilizerMoveChain_substitute", "Atlas.GroupTheory.PrimitivePointChains", "theorem"), ("Atlas.GroupTheory.stabilizerMoveChain_symm", "Atlas.GroupTheory.PrimitivePointChains", "theorem"), ("Atlas.GroupTheory.stabilizerMoveClosure", "Atlas.GroupTheory.PrimitivePointChains", "any"), ("Atlas.GroupTheory.stabilizerMoveClosure_image", "Atlas.GroupTheory.PrimitivePointChainTransport", "theorem"), ("Atlas.GroupTheory.stabilizerMoveClosure_subset_block", "Atlas.GroupTheory.PrimitivePointChains", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/f4-point-primitivity/20260928T054813-642195"
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
