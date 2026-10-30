import Atlas.LinearGroups.Chevalley.TwistedE6.E6OrderPolynomial
import Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry
import Atlas.LinearGroups.Chevalley.TwistedE6.FoldedRootWords
import Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery
import Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery
import Atlas.LinearGroups.Chevalley.TwistedE6.OrbitProductEquivariance
import Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates
import Atlas.LinearGroups.Chevalley.TwistedE6.WeightedRootInversions
import Atlas.LinearGroups.Chevalley.TwistedE6.WitnessedPositiveProduct
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Chevalley.Integral.Minuscule.Strings.commute_roots_of_quadratic_pair", "Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery", "theorem"), ("Atlas.Chevalley.Integral.Minuscule.Strings.commute_step_of_root_one", "Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery", "theorem"), ("Atlas.Chevalley.Integral.Minuscule.Strings.commute_steps_of_quadratic_pair", "Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery", "theorem"), ("Atlas.Chevalley.TwistedE6.ClosedOrder.weightedWeylPolynomial", "Atlas.LinearGroups.Chevalley.TwistedE6.E6OrderPolynomial", "definition"), ("Atlas.Chevalley.TwistedE6.ClosedOrder.weightedWeylPolynomial_bruhat", "Atlas.LinearGroups.Chevalley.TwistedE6.E6OrderPolynomial", "theorem"), ("Atlas.Chevalley.TwistedE6.ClosedOrder.weightedWeylPolynomial_torus", "Atlas.LinearGroups.Chevalley.TwistedE6.E6OrderPolynomial", "theorem"), ("Atlas.Chevalley.TwistedE6.WeightedRootInversions.erased_weightedInversions_mul_simple", "Atlas.LinearGroups.Chevalley.TwistedE6.WeightedRootInversions", "theorem"), ("Atlas.Chevalley.TwistedE6.WeightedRootInversions.weightedInversions", "Atlas.LinearGroups.Chevalley.TwistedE6.WeightedRootInversions", "definition"), ("Atlas.Chevalley.TwistedE6.WeightedRootInversions.weightedInversions_mul_simple_of_negative", "Atlas.LinearGroups.Chevalley.TwistedE6.WeightedRootInversions", "theorem"), ("Atlas.Chevalley.TwistedE6.WeightedRootInversions.weightedInversions_mul_simple_of_positive", "Atlas.LinearGroups.Chevalley.TwistedE6.WeightedRootInversions", "theorem"), ("Atlas.Chevalley.TwistedE6.WeightedRootInversions.weightedInversions_one", "Atlas.LinearGroups.Chevalley.TwistedE6.WeightedRootInversions", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PositiveRootEnumeration", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "definition"), ("Atlas.Chevalley.TwistedE6.e6PositiveRootEnumeration_bijective", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PositiveRootEnumeration_coordinates", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PositiveRootEnumeration_injective", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PositiveRootEnumeration_surjective", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PositiveRootEquiv", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "definition"), ("Atlas.Chevalley.TwistedE6.e6PositiveRootEquiv_coordinates", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6_height_eq_coordinate_sum", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6_isPos_iff_coordinates_nonnegative", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6_isPos_iff_representative", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6_isPos_of_coordinates_nonnegative", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6_positive_root_exhaustion", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6_representative_isPos", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.e6_rootRepresentative_injective", "Atlas.LinearGroups.Chevalley.TwistedE6.PositiveCoordinates", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedReflectionLift_diagram", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedReflectionLift_involutive", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedReflectionLift_norm", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedRootSeed", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedRootWords", "definition"), ("Atlas.Chevalley.TwistedE6.foldedRootSeed_fixed_iff", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedRootWords", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedRootWord", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedRootWords", "definition"), ("Atlas.Chevalley.TwistedE6.foldedRootWordAction", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedRootWords", "definition"), ("Atlas.Chevalley.TwistedE6.foldedRootWordAction_diagram", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedRootWordAction_injective", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedRootWordAction_norm", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedRootWord_partner", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedReflectionGeometry", "theorem"), ("Atlas.Chevalley.TwistedE6.foldedRootWord_representative", "Atlas.LinearGroups.Chevalley.TwistedE6.FoldedRootWords", "theorem"), ("Atlas.Chevalley.TwistedE6.positiveOrbitBlock_twist", "Atlas.LinearGroups.Chevalley.TwistedE6.OrbitProductEquivariance", "theorem"), ("Atlas.Chevalley.TwistedE6.positiveOrbitBlocks_twist", "Atlas.LinearGroups.Chevalley.TwistedE6.OrbitProductEquivariance", "theorem"), ("Atlas.Chevalley.TwistedE6.positiveOrbitProduct", "Atlas.LinearGroups.Chevalley.TwistedE6.OrbitProductEquivariance", "definition"), ("Atlas.Chevalley.TwistedE6.positiveOrbitProduct_fixed_iff", "Atlas.LinearGroups.Chevalley.TwistedE6.OrbitProductEquivariance", "theorem"), ("Atlas.Chevalley.TwistedE6.positiveOrbitProduct_twist", "Atlas.LinearGroups.Chevalley.TwistedE6.OrbitProductEquivariance", "theorem"), ("Atlas.Chevalley.positiveRootWitnessedProduct", "Atlas.LinearGroups.Chevalley.TwistedE6.WitnessedPositiveProduct", "definition"), ("Atlas.Chevalley.positiveRootWitnessedProductEquiv", "Atlas.LinearGroups.Chevalley.TwistedE6.WitnessedPositiveProduct", "definition"), ("Atlas.Chevalley.positiveRootWitnessedProduct_injective", "Atlas.LinearGroups.Chevalley.TwistedE6.WitnessedPositiveProduct", "theorem"), ("Atlas.Chevalley.positiveRootWitnessedProduct_surjective", "Atlas.LinearGroups.Chevalley.TwistedE6.WitnessedPositiveProduct", "theorem"), ("Atlas.Chevalley.positiveRootWitnessedProduct_val", "Atlas.LinearGroups.Chevalley.TwistedE6.WitnessedPositiveProduct", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.affine_pair_expansion", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.commute_affine", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.commute_coefficients_of_polynomial", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.commute_of_one_add", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.commute_pair_of_affine_product", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.commute_pair_of_card_square", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.commute_pair_of_quadratic_extension", "Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.frobenius_pair_expansion", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.scalar_coefficients_eq_zero", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem"), ("Atlas.LinearAlgebra.MatrixCentralizer.succ_lt_square", "Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "/home/gerald/atlas/claude/release-update-v1.2-20261030/verification-runs/20261030T095408-audit-batch-batch-013-twisted-e6"
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
