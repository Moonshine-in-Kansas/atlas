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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Arithmetic.geometricSum", "Atlas.Algebra.GeometricSumBounds", "definition"), ("Atlas.Arithmetic.geometricSum_gt_one", "Atlas.Algebra.GeometricSumBounds", "theorem"), ("Atlas.Arithmetic.geometricSum_lt_power", "Atlas.Algebra.GeometricSumBounds", "theorem"), ("Atlas.Arithmetic.geometricSum_shift", "Atlas.Algebra.GeometricSumBounds", "theorem"), ("Atlas.Arithmetic.geometricSum_succ", "Atlas.Algebra.GeometricSumBounds", "theorem"), ("Atlas.Arithmetic.geometric_block_nondivisibility", "Atlas.Algebra.GeometricSumBounds", "theorem"), ("Atlas.LinearAlgebra.projectiveSubmoduleEquiv", "Atlas.LinearAlgebra.ProjectiveSubmodule", "definition"), ("Atlas.Symplectic.Orthogonal", "Atlas.LinearGroups.Symplectic.PointGeometry", "definition"), ("Atlas.Symplectic.Points", "Atlas.LinearGroups.Symplectic.Projective", "definition"), ("Atlas.Symplectic.abelian_transvection_images", "Atlas.LinearGroups.Symplectic.AbelianImages", "theorem"), ("Atlas.Symplectic.binary_seven_transvections", "Atlas.LinearGroups.Symplectic.BinaryIdentity", "theorem"), ("Atlas.Symplectic.card_lineTransvections", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.card_perpendicular_points", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.card_perpendicular_points_sum", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.card_points", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.card_points_sum", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.card_suborbit_one", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.card_suborbit_two", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.card_suborbit_two_power", "Atlas.LinearGroups.Symplectic.Primitivity", "theorem"), ("Atlas.Symplectic.card_suborbit_zero", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.directionGroup", "Atlas.LinearGroups.Symplectic.LineTransvections", "definition"), ("Atlas.Symplectic.directionGroup_conj", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.directionGroup_scale", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.ePoint", "Atlas.LinearGroups.Symplectic.PointGeometry", "definition"), ("Atlas.Symplectic.e_nonzero", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.exists_generated_send", "Atlas.LinearGroups.Symplectic.GeneratedAction", "theorem"), ("Atlas.Symplectic.exists_generated_send_fix", "Atlas.LinearGroups.Symplectic.GeneratedAction", "theorem"), ("Atlas.Symplectic.exists_isometry_orthogonal_pair", "Atlas.LinearGroups.Symplectic.OrthogonalFrame", "theorem"), ("Atlas.Symplectic.exists_pairing_both", "Atlas.LinearGroups.Symplectic.GeneratedAction", "theorem"), ("Atlas.Symplectic.exists_projective_send", "Atlas.LinearGroups.Symplectic.ProjectiveGeneration", "theorem"), ("Atlas.Symplectic.exists_scalar_square_ne_one", "Atlas.LinearGroups.Symplectic.PerfectLarge", "theorem"), ("Atlas.Symplectic.extendHom", "Atlas.LinearGroups.Symplectic.Generation", "definition"), ("Atlas.Symplectic.extendHom_apply", "Atlas.LinearGroups.Symplectic.Generation", "theorem"), ("Atlas.Symplectic.extend_mem_generated", "Atlas.LinearGroups.Symplectic.Generation", "theorem"), ("Atlas.Symplectic.extend_transvection", "Atlas.LinearGroups.Symplectic.Generation", "theorem"), ("Atlas.Symplectic.fPoint", "Atlas.LinearGroups.Symplectic.PointGeometry", "definition"), ("Atlas.Symplectic.f_nonzero", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.fixes_points_iff_central", "Atlas.LinearGroups.Symplectic.Projective", "theorem"), ("Atlas.Symplectic.headTail_e_succ", "Atlas.LinearGroups.Symplectic.OrthogonalFrame", "theorem"), ("Atlas.Symplectic.iwasawa", "Atlas.LinearGroups.Symplectic.LineTransvections", "definition"), ("Atlas.Symplectic.lineTransvections", "Atlas.LinearGroups.Symplectic.LineTransvections", "definition"), ("Atlas.Symplectic.lineTransvections_abelian", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.lineTransvections_conj", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.lineTransvections_generate", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.lineTransvections_le_stabilizer", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.lineTransvections_mk", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.lineTransvections_normal", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.mem_directionGroup", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.mem_transvectionGroup", "Atlas.LinearGroups.Symplectic.Generation", "theorem"), ("Atlas.Symplectic.nonorthogonal_stabilizer_transitive", "Atlas.LinearGroups.Symplectic.PointOrbits", "theorem"), ("Atlas.Symplectic.normalize_nonorthogonal_pair", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.normalize_orthogonal_pair", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.orthogonal_mk", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.orthogonal_self", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.orthogonal_smul", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.orthogonal_stabilizer_transitive", "Atlas.LinearGroups.Symplectic.PointOrbits", "theorem"), ("Atlas.Symplectic.orthogonal_symm", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.parameterHom", "Atlas.LinearGroups.Symplectic.LineTransvections", "definition"), ("Atlas.Symplectic.perfect_of_abelian_images", "Atlas.LinearGroups.Symplectic.AbelianImages", "theorem"), ("Atlas.Symplectic.perfect_of_card_gt_three", "Atlas.LinearGroups.Symplectic.PerfectLarge", "theorem"), ("Atlas.Symplectic.perfect_of_card_three", "Atlas.LinearGroups.Symplectic.PerfectThree", "theorem"), ("Atlas.Symplectic.perfect_of_card_two", "Atlas.LinearGroups.Symplectic.PerfectTwo", "theorem"), ("Atlas.Symplectic.perfect_of_good", "Atlas.LinearGroups.Symplectic.Perfectness", "theorem"), ("Atlas.Symplectic.perfect_of_transvections", "Atlas.LinearGroups.Symplectic.PerfectLarge", "theorem"), ("Atlas.Symplectic.perpendicularPointsEquiv", "Atlas.LinearGroups.Symplectic.PointCount", "definition"), ("Atlas.Symplectic.pointPerm", "Atlas.LinearGroups.Symplectic.Projective", "definition"), ("Atlas.Symplectic.pointPerm_kernel", "Atlas.LinearGroups.Symplectic.Projective", "theorem"), ("Atlas.Symplectic.pointSum", "Atlas.LinearGroups.Symplectic.PointCount", "definition"), ("Atlas.Symplectic.projection_smul", "Atlas.LinearGroups.Symplectic.Projective", "theorem"), ("Atlas.Symplectic.projection_transvection_ne_one", "Atlas.LinearGroups.Symplectic.Nontrivial", "theorem"), ("Atlas.Symplectic.projectiveAction", "Atlas.LinearGroups.Symplectic.Projective", "any"), ("Atlas.Symplectic.projectivePerm", "Atlas.LinearGroups.Symplectic.Projective", "definition"), ("Atlas.Symplectic.projectiveTransvectionGroup", "Atlas.LinearGroups.Symplectic.ProjectiveGeneration", "definition"), ("Atlas.Symplectic.projectiveTransvectionGroup_eq_top", "Atlas.LinearGroups.Symplectic.ProjectiveGeneration", "theorem"), ("Atlas.Symplectic.projective_faithful", "Atlas.LinearGroups.Symplectic.Projective", "any"), ("Atlas.Symplectic.projective_nontrivial", "Atlas.LinearGroups.Symplectic.Nontrivial", "theorem"), ("Atlas.Symplectic.projective_not_commutative", "Atlas.LinearGroups.Symplectic.Noncommutative", "theorem"), ("Atlas.Symplectic.projective_orthogonal_smul", "Atlas.LinearGroups.Symplectic.PointGeometry", "theorem"), ("Atlas.Symplectic.projective_parameter_injective", "Atlas.LinearGroups.Symplectic.LineTransvections", "theorem"), ("Atlas.Symplectic.projective_perfect_of_card_gt_three", "Atlas.LinearGroups.Symplectic.PerfectLarge", "theorem"), ("Atlas.Symplectic.projective_perfect_of_good", "Atlas.LinearGroups.Symplectic.Perfectness", "theorem"), ("Atlas.Symplectic.projective_preprimitive", "Atlas.LinearGroups.Symplectic.Primitivity", "theorem"), ("Atlas.Symplectic.projective_pretransitive", "Atlas.LinearGroups.Symplectic.ProjectiveGeneration", "any"), ("Atlas.Symplectic.rankOneIndex", "Atlas.LinearGroups.Symplectic.RankOne", "definition"), ("Atlas.Symplectic.rankOnePSL", "Atlas.LinearGroups.Symplectic.RankOne", "definition"), ("Atlas.Symplectic.rankOnePSL_projection", "Atlas.LinearGroups.Symplectic.RankOne", "theorem"), ("Atlas.Symplectic.rankOneSL", "Atlas.LinearGroups.Symplectic.RankOne", "definition"), ("Atlas.Symplectic.rankOneSL_action", "Atlas.LinearGroups.Symplectic.RankOne", "theorem"), ("Atlas.Symplectic.rankOneVector", "Atlas.LinearGroups.Symplectic.RankOne", "definition"), ("Atlas.Symplectic.rankOne_form_mul", "Atlas.LinearGroups.Symplectic.RankOne", "theorem"), ("Atlas.Symplectic.rankOne_mem_iff_det", "Atlas.LinearGroups.Symplectic.RankOne", "theorem"), ("Atlas.Symplectic.simple_high_rank", "Atlas.LinearGroups.Symplectic.SimplicityHighRank", "theorem"), ("Atlas.Symplectic.simple_of_good", "Atlas.LinearGroups.Symplectic.Simplicity", "theorem"), ("Atlas.Symplectic.simple_rank_one", "Atlas.LinearGroups.Symplectic.Simplicity", "theorem"), ("Atlas.Symplectic.stabilizer_orbit_iff", "Atlas.LinearGroups.Symplectic.PointOrbits", "theorem"), ("Atlas.Symplectic.suborbitIndex", "Atlas.LinearGroups.Symplectic.PointOrbits", "definition"), ("Atlas.Symplectic.suborbitIndex_eq_one_iff", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.suborbitIndex_eq_two_iff", "Atlas.LinearGroups.Symplectic.PointCount", "theorem"), ("Atlas.Symplectic.suborbitIndex_invariant", "Atlas.LinearGroups.Symplectic.PointOrbits", "theorem"), ("Atlas.Symplectic.suborbitIndex_self", "Atlas.LinearGroups.Symplectic.PointOrbits", "theorem"), ("Atlas.Symplectic.suborbitIndex_transitive", "Atlas.LinearGroups.Symplectic.PointOrbits", "theorem"), ("Atlas.Symplectic.ternary_four_transvections", "Atlas.LinearGroups.Symplectic.TernaryIdentity", "theorem"), ("Atlas.Symplectic.transvectionGroup", "Atlas.LinearGroups.Symplectic.GeneratedAction", "definition"), ("Atlas.Symplectic.transvectionGroup_eq_top", "Atlas.LinearGroups.Symplectic.Generation", "theorem"), ("Atlas.Symplectic.transvection_fixes_of_orthogonal", "Atlas.LinearGroups.Symplectic.GeneratedAction", "theorem"), ("Atlas.Symplectic.transvection_mem", "Atlas.LinearGroups.Symplectic.GeneratedAction", "theorem"), ("Atlas.Symplectic.transvection_mem_commutator_of_scalar", "Atlas.LinearGroups.Symplectic.PerfectLarge", "theorem"), ("Atlas.Symplectic.transvection_pow", "Atlas.LinearGroups.Symplectic.AbelianImages", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/symplectic-simplicity/20260914T065248-230"
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
