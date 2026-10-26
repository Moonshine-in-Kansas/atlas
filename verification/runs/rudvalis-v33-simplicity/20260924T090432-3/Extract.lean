import Atlas.GroupTheory.InvariantOrbitDivisibility
import Atlas.GroupTheory.OneSuborbitPrimitivity
import Atlas.GroupTheory.PerfectSimpleQuotient
import Atlas.GroupTheory.PrimitivePerfectFrameSimplicity
import Atlas.Rudvalis.FourActiveLabelAction
import Atlas.Rudvalis.FourSuborbitDivisibility
import Atlas.Rudvalis.FrameLinearSimplicity
import Atlas.Rudvalis.FrameTranslationCommutators
import Atlas.Rudvalis.NonorthogonalSuborbits
import Atlas.Rudvalis.ProjectiveFrameEmbedding
import Atlas.Rudvalis.ProjectiveFrameFiltration
import Atlas.Rudvalis.ProjectiveMatrixFiltration
import Atlas.Rudvalis.ProjectivePrimitivity
import Atlas.Rudvalis.ProjectiveSignFiltration
import Atlas.Rudvalis.ProjectiveSimplicity
import Atlas.Rudvalis.ReferenceLinearLifts
import Atlas.Sporadic.Rudvalis
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.GroupTheory.invariant_card_dvd_of_orbits", "Atlas.GroupTheory.InvariantOrbitDivisibility", "theorem"), ("Atlas.GroupTheory.normal_eq_top_of_odd_index_involution", "Atlas.GroupTheory.PrimitivePerfectFrameSimplicity", "theorem"), ("Atlas.GroupTheory.normal_quotient_card_dvd_stabilizer", "Atlas.GroupTheory.PrimitivePerfectFrameSimplicity", "theorem"), ("Atlas.GroupTheory.perfect_hom_trivial_of_simple_quotient", "Atlas.GroupTheory.PerfectSimpleQuotient", "theorem"), ("Atlas.GroupTheory.primitive_of_one_suborbit_divisible_rest", "Atlas.GroupTheory.OneSuborbitPrimitivity", "theorem"), ("Atlas.GroupTheory.simple_of_primitive_perfect_frame", "Atlas.GroupTheory.PrimitivePerfectFrameSimplicity", "theorem"), ("Atlas.GroupTheory.stabilizer_quotient_surjective_of_normal_transitive", "Atlas.GroupTheory.PrimitivePerfectFrameSimplicity", "theorem"), ("Atlas.Rudvalis.ActiveFourLabels", "Atlas.Rudvalis.FourSuborbitDivisibility", "definition"), ("Atlas.Rudvalis.ProjectiveTranslationModule", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "definition"), ("Atlas.Rudvalis.activeFormTransvection", "Atlas.Rudvalis.ReferenceLinearLifts", "definition"), ("Atlas.Rudvalis.activeFormTransvection_dual", "Atlas.Rudvalis.ReferenceLinearLifts", "theorem"), ("Atlas.Rudvalis.activeFormTransvection_fixed", "Atlas.Rudvalis.ReferenceLinearLifts", "theorem"), ("Atlas.Rudvalis.activeFourLabels_card", "Atlas.Rudvalis.FourSuborbitDivisibility", "theorem"), ("Atlas.Rudvalis.binaryLinearGroup_simple", "Atlas.Rudvalis.FrameLinearSimplicity", "theorem"), ("Atlas.Rudvalis.binaryLinearGroup_simple_order", "Atlas.Rudvalis.FrameLinearSimplicity", "theorem"), ("Atlas.Rudvalis.binaryPSLLinearEquiv", "Atlas.Rudvalis.FrameLinearSimplicity", "definition"), ("Atlas.Rudvalis.binarySLLinearEquiv", "Atlas.Rudvalis.FrameLinearSimplicity", "definition"), ("Atlas.Rudvalis.binarySLToLinear_injective", "Atlas.Rudvalis.FrameLinearSimplicity", "theorem"), ("Atlas.Rudvalis.binarySL_center_eq_bot", "Atlas.Rudvalis.FrameLinearSimplicity", "theorem"), ("Atlas.Rudvalis.codeGroup_commutator_scalars_eq_top", "Atlas.Rudvalis.FrameTranslationCommutators", "theorem"), ("Atlas.Rudvalis.codeGroup_eq_top_of_commutator_and_I", "Atlas.Rudvalis.FrameTranslationCommutators", "theorem"), ("Atlas.Rudvalis.codeI_blockLinear", "Atlas.Rudvalis.ProjectiveFrameFiltration", "theorem"), ("Atlas.Rudvalis.codeI_translation_identity", "Atlas.Rudvalis.FrameTranslationCommutators", "theorem"), ("Atlas.Rudvalis.codeProjectiveHom", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "definition"), ("Atlas.Rudvalis.codeProjectiveHom_kernel", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.codeReferenceStabilizer_active_forms", "Atlas.Rudvalis.FourActiveLabelAction", "theorem"), ("Atlas.Rudvalis.codeReferenceStabilizer_linear_lift", "Atlas.Rudvalis.ReferenceLinearLifts", "theorem"), ("Atlas.Rudvalis.codeReference_nonorthogonal_orbit_divisible", "Atlas.Rudvalis.NonorthogonalSuborbits", "theorem"), ("Atlas.Rudvalis.codeReference_orbit_nonorthogonal", "Atlas.Rudvalis.FourSuborbitDivisibility", "theorem"), ("Atlas.Rudvalis.codeRowMatrixHom_eq_one_iff", "Atlas.Rudvalis.ProjectiveSignFiltration", "theorem"), ("Atlas.Rudvalis.coordinateCross_stabilizer_linear_lift", "Atlas.Rudvalis.ReferenceLinearLifts", "theorem"), ("Atlas.Rudvalis.fourCrossHasLabel_active", "Atlas.Rudvalis.FourActiveLabelAction", "theorem"), ("Atlas.Rudvalis.fourCrossHasLabel_transport", "Atlas.Rudvalis.FourActiveLabelAction", "theorem"), ("Atlas.Rudvalis.fourCrossHasLabel_unique", "Atlas.Rudvalis.FourActiveLabelAction", "theorem"), ("Atlas.Rudvalis.fourCross_rowReference_orbit_divisible", "Atlas.Rudvalis.FourSuborbitDivisibility", "theorem"), ("Atlas.Rudvalis.fourReferenceOrbitLabelEquiv", "Atlas.Rudvalis.FourSuborbitDivisibility", "definition"), ("Atlas.Rudvalis.fourReferenceOrbitLabelFibre", "Atlas.Rudvalis.FourSuborbitDivisibility", "definition"), ("Atlas.Rudvalis.fourReferenceOrbitLabelFibre_divisible", "Atlas.Rudvalis.FourSuborbitDivisibility", "theorem"), ("Atlas.Rudvalis.four_reference_orbit_divisible", "Atlas.Rudvalis.FourSuborbitDivisibility", "theorem"), ("Atlas.Rudvalis.four_reference_orbit_range", "Atlas.Rudvalis.FourSuborbitDivisibility", "theorem"), ("Atlas.Rudvalis.full_gaussian_center_eq_scalars", "Atlas.Rudvalis.ProjectiveSimplicity", "theorem"), ("Atlas.Rudvalis.gaussianUnits_le_codeRowKernel", "Atlas.Rudvalis.ProjectiveFrameFiltration", "theorem"), ("Atlas.Rudvalis.heavyCross_rowReference_orbit_divisible", "Atlas.Rudvalis.NonorthogonalSuborbits", "theorem"), ("Atlas.Rudvalis.heavy_reference_orbit_divisible", "Atlas.Rudvalis.NonorthogonalSuborbits", "theorem"), ("Atlas.Rudvalis.matrixScalarLine", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "definition"), ("Atlas.Rudvalis.matrixScalarLine_finrank", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.projectiveCodeBlockHom", "Atlas.Rudvalis.ProjectiveFrameFiltration", "definition"), ("Atlas.Rudvalis.projectiveCodeBlockHom_kernel_order", "Atlas.Rudvalis.ProjectiveFrameFiltration", "theorem"), ("Atlas.Rudvalis.projectiveCodeBlockHom_kernel_solvable", "Atlas.Rudvalis.ProjectiveFrameFiltration", "theorem"), ("Atlas.Rudvalis.projectiveCodeBlockHom_mk", "Atlas.Rudvalis.ProjectiveFrameFiltration", "theorem"), ("Atlas.Rudvalis.projectiveCodeBlockHom_surjective", "Atlas.Rudvalis.ProjectiveFrameFiltration", "theorem"), ("Atlas.Rudvalis.projectiveCodeGroup_perfect", "Atlas.Rudvalis.FrameTranslationCommutators", "theorem"), ("Atlas.Rudvalis.projectiveCodeHom", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "definition"), ("Atlas.Rudvalis.projectiveCodeHom_injective", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.projectiveFrameEquiv", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "definition"), ("Atlas.Rudvalis.projectiveFrameGroup", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "definition"), ("Atlas.Rudvalis.projectiveFrameGroup_index", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.projectiveFrameGroup_index_odd", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.projectiveFrameGroup_mem_iff", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.projectiveFrameGroup_order", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.projectiveFrameGroup_perfect", "Atlas.Rudvalis.ProjectiveSimplicity", "theorem"), ("Atlas.Rudvalis.projectiveFrameGroup_reflection_generate", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.projectiveReflection", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "definition"), ("Atlas.Rudvalis.projectiveReflection_square", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.projectiveRowKernel", "Atlas.Rudvalis.ProjectiveFrameFiltration", "definition"), ("Atlas.Rudvalis.projectiveRowMatrixHom", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "definition"), ("Atlas.Rudvalis.projectiveRowMatrixHom_kernel_eq_signs", "Atlas.Rudvalis.ProjectiveSignFiltration", "theorem"), ("Atlas.Rudvalis.projectiveRowMatrixHom_kernel_order", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.projectiveRowMatrixHom_projection", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.projectiveRowMatrixHom_surjective", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.projectiveRowProjection", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "definition"), ("Atlas.Rudvalis.projectiveRowProjection_kernel", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.projectiveRowProjection_scalar_case", "Atlas.Rudvalis.ProjectiveSignFiltration", "theorem"), ("Atlas.Rudvalis.projectiveRowProjection_surjective", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.projectiveSignHom", "Atlas.Rudvalis.ProjectiveSignFiltration", "definition"), ("Atlas.Rudvalis.projectiveSignKernel", "Atlas.Rudvalis.ProjectiveSignFiltration", "definition"), ("Atlas.Rudvalis.projectiveSignKernel_finrank", "Atlas.Rudvalis.ProjectiveSignFiltration", "theorem"), ("Atlas.Rudvalis.projectiveSignKernel_le_matrixKernel", "Atlas.Rudvalis.ProjectiveSignFiltration", "theorem"), ("Atlas.Rudvalis.projectiveSignKernel_order", "Atlas.Rudvalis.ProjectiveSignFiltration", "theorem"), ("Atlas.Rudvalis.projectiveSignKernel_square", "Atlas.Rudvalis.ProjectiveSignFiltration", "theorem"), ("Atlas.Rudvalis.projectiveTranslationModule_card", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.projectiveTranslationModule_finrank", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.rowGaussianI", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "definition"), ("Atlas.Rudvalis.rowGaussianI_matrix", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.rowGaussianI_matrixQuotient", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.rowMatrixQuotientHom", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "definition"), ("Atlas.Rudvalis.rowMatrixQuotientHom_kills_scalars", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.rowMatrixQuotientHom_surjective", "Atlas.Rudvalis.ProjectiveMatrixFiltration", "theorem"), ("Atlas.Rudvalis.rowReferenceToCodeReference", "Atlas.Rudvalis.FourSuborbitDivisibility", "definition"), ("Atlas.Rudvalis.rowSignKernelHom", "Atlas.Rudvalis.ProjectiveSignFiltration", "definition"), ("Atlas.Rudvalis.rudvalisGroup_nontrivial", "Atlas.Rudvalis.ProjectiveFrameEmbedding", "theorem"), ("Atlas.Rudvalis.rudvalis_block_arithmetic", "Atlas.Rudvalis.ProjectivePrimitivity", "theorem"), ("Atlas.Rudvalis.rudvalis_center_eq_bot", "Atlas.Rudvalis.ProjectiveSimplicity", "theorem"), ("Atlas.Rudvalis.rudvalis_cross_primitive", "Atlas.Rudvalis.ProjectivePrimitivity", "theorem"), ("Atlas.Rudvalis.rudvalis_nonabelian", "Atlas.Rudvalis.ProjectiveSimplicity", "theorem"), ("Atlas.Rudvalis.rudvalis_noncommutative", "Atlas.Rudvalis.ProjectiveSimplicity", "theorem"), ("Atlas.Rudvalis.rudvalis_simple", "Atlas.Rudvalis.ProjectiveSimplicity", "theorem"), ("Atlas.Rudvalis.rudvalis_simple_of_primitive_frame_quotient", "Atlas.Rudvalis.ProjectiveSimplicity", "theorem"), ("Atlas.Rudvalis.translationPreimage", "Atlas.Rudvalis.FrameTranslationCommutators", "definition"), ("Atlas.Rudvalis.translationPreimage_eq_top", "Atlas.Rudvalis.FrameTranslationCommutators", "theorem"), ("Atlas.Rudvalis.translations_le_commutator_scalars", "Atlas.Rudvalis.FrameTranslationCommutators", "theorem"), ("Atlas.Sporadic.Rudvalis.exists_mul_ne_mul", "Atlas.Sporadic.Rudvalis", "theorem"), ("Atlas.Sporadic.Rudvalis.isSimpleGroup", "Atlas.Sporadic.Rudvalis", "theorem"), ("Atlas.Sporadic.Rudvalis.nonabelian", "Atlas.Sporadic.Rudvalis", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/rudvalis-v33-simplicity/20260924T090432-3"
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
