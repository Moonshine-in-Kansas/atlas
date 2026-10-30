import Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows
import Atlas.LinearGroups.ReeF4.OppositePairIntrinsicSpace
import Atlas.LinearGroups.ReeF4.OppositePairRecognition
import Atlas.LinearGroups.ReeF4.OppositePairRestriction
import Atlas.LinearGroups.ReeF4.OppositePairRestrictionFaithful
import Atlas.LinearGroups.ReeF4.OppositePairStabilizer
import Atlas.LinearGroups.ReeF4.OppositePairTensorPreservation
import Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicSymplectic
import Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor
import Atlas.LinearGroups.SuzukiFamily.TensorAction
import Atlas.LinearGroups.SuzukiFamily.TensorDiagonal
import Atlas.LinearGroups.SuzukiFamily.TensorRecognition
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.ReeF4.eq_modelSuzukiEmbedding_of_restriction", "Atlas.LinearGroups.ReeF4.OppositePairRestrictionFaithful", "theorem"), ("Atlas.ReeF4.fullOppositePairSuzukiEquiv", "Atlas.LinearGroups.ReeF4.OppositePairStabilizer", "definition"), ("Atlas.ReeF4.isotropyCross_row0", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row1", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row10", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row11", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row12", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row13", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row14", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row15", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row16", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row17", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row18", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row19", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row2", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row20", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row21", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row22", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row23", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row24", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row25", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row3", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row4", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row5", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row6", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row7", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row8", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyCross_row9", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row0", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row1", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row10", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row11", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row12", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row13", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row14", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row15", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row16", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row17", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row18", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row19", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row2", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row20", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row21", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row22", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row23", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row24", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row25", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row3", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row4", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row5", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row6", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row7", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row8", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.isotropyRawStar_row9", "Atlas.LinearGroups.ReeF4.IsotropyCoordinateRows", "theorem"), ("Atlas.ReeF4.mem_baseSpecialOppositePair_stabilizer_iff", "Atlas.LinearGroups.ReeF4.OppositePairStabilizer", "theorem"), ("Atlas.ReeF4.mem_negativeSuzukiBlock_iff_intrinsicImage", "Atlas.LinearGroups.ReeF4.OppositePairIntrinsicSpace", "theorem"), ("Atlas.ReeF4.modelSuzukiEmbedding_fixes_first", "Atlas.LinearGroups.ReeF4.OppositePairRestrictionFaithful", "theorem"), ("Atlas.ReeF4.modelSuzukiEmbedding_fixes_opposite", "Atlas.LinearGroups.ReeF4.OppositePairRestrictionFaithful", "theorem"), ("Atlas.ReeF4.modelSuzukiEmbedding_restriction_apply", "Atlas.LinearGroups.ReeF4.OppositePairRestrictionFaithful", "theorem"), ("Atlas.ReeF4.model_ext_oppositePair_block", "Atlas.LinearGroups.ReeF4.OppositePairRestrictionFaithful", "theorem"), ("Atlas.ReeF4.oppositePairImagePreimage", "Atlas.LinearGroups.ReeF4.OppositePairIntrinsicSpace", "definition"), ("Atlas.ReeF4.oppositePairImagePreimage_domain", "Atlas.LinearGroups.ReeF4.OppositePairIntrinsicSpace", "theorem"), ("Atlas.ReeF4.oppositePairImagePreimage_image", "Atlas.LinearGroups.ReeF4.OppositePairIntrinsicSpace", "theorem"), ("Atlas.ReeF4.oppositePairImage_formula", "Atlas.LinearGroups.ReeF4.OppositePairIntrinsicSpace", "theorem"), ("Atlas.ReeF4.oppositePairLinearRestriction", "Atlas.LinearGroups.ReeF4.OppositePairRestriction", "definition"), ("Atlas.ReeF4.oppositePairLinearRestriction_block2", "Atlas.LinearGroups.ReeF4.OppositePairTensorPreservation", "theorem"), ("Atlas.ReeF4.oppositePairLinearRestriction_embed", "Atlas.LinearGroups.ReeF4.OppositePairRestriction", "theorem"), ("Atlas.ReeF4.oppositePairLinearRestriction_injective", "Atlas.LinearGroups.ReeF4.OppositePairRestrictionFaithful", "theorem"), ("Atlas.ReeF4.oppositePairLinearRestriction_polar", "Atlas.LinearGroups.ReeF4.OppositePairTensorPreservation", "theorem"), ("Atlas.ReeF4.oppositePairLinearRestriction_tensor", "Atlas.LinearGroups.ReeF4.OppositePairTensorPreservation", "theorem"), ("Atlas.ReeF4.oppositePairStabilizer_eq_suzukiProduct", "Atlas.LinearGroups.ReeF4.OppositePairStabilizer", "theorem"), ("Atlas.ReeF4.oppositePair_fixes_minus3", "Atlas.LinearGroups.ReeF4.OppositePairTensorPreservation", "theorem"), ("Atlas.ReeF4.oppositePair_preserves_negativeBlock", "Atlas.LinearGroups.ReeF4.OppositePairRestriction", "theorem"), ("Atlas.ReeF4.oppositeVectorStabilizer_eq_suzuki", "Atlas.LinearGroups.ReeF4.OppositePairRecognition", "theorem"), ("Atlas.ReeF4.suzukiIntrinsicCoordinates_injective", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsicPolar", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "definition"), ("Atlas.ReeF4.suzukiIntrinsicRawTensor", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "definition"), ("Atlas.ReeF4.suzukiIntrinsic_block1_coordinates", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_block2_coordinates", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_block3_coordinates", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_cross_minus3", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_cross_plus", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_map_block3", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_map_firstRoot_smul", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicSymplectic", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_mixed_cross", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_mixed_domain", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_mixed_polar", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_mixed_rawStar", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_same_cross", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicSymplectic", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_same_domain", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicSymplectic", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_same_partial", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicSymplectic", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_same_polar", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicSymplectic", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_same_rawStar", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicSymplectic", "theorem"), ("Atlas.ReeF4.suzukiIntrinsic_tensor_actual", "Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicTensor", "theorem"), ("Atlas.SuzukiFamily.IsTensorSpecial", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "definition"), ("Atlas.SuzukiFamily.IsTensorSpecial.map", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "theorem"), ("Atlas.SuzukiFamily.IsTensorSpecial.smul", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "theorem"), ("Atlas.SuzukiFamily.PreservesPartialTensor", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "definition"), ("Atlas.SuzukiFamily.partialTensor", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "definition"), ("Atlas.SuzukiFamily.partialTensor_basis01", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "theorem"), ("Atlas.SuzukiFamily.partialTensor_basis02", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "theorem"), ("Atlas.SuzukiFamily.partialTensor_preserves_column01", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "theorem"), ("Atlas.SuzukiFamily.partialTensor_preserves_column02", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "theorem"), ("Atlas.SuzukiFamily.rawPartialTensor", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "definition"), ("Atlas.SuzukiFamily.rawPartialTensor_smul", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "theorem"), ("Atlas.SuzukiFamily.tensorBasis", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "definition"), ("Atlas.SuzukiFamily.tensorBasis_special_first", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "theorem"), ("Atlas.SuzukiFamily.tensorBasis_special_last", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "theorem"), ("Atlas.SuzukiFamily.tensorPolar", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "definition"), ("Atlas.SuzukiFamily.tensorPolar_smul", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "theorem"), ("Atlas.SuzukiFamily.tensorSpecial_affine_normalized", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "theorem"), ("Atlas.SuzukiFamily.tensorSpecial_projective_mem", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "theorem"), ("Atlas.SuzukiFamily.tensorSpecial_zero_first", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "theorem"), ("Atlas.SuzukiFamily.tensor_diagonal_parameters", "Atlas.LinearGroups.SuzukiFamily.TensorRecognition", "theorem"), ("Atlas.SuzukiFamily.tensor_linear_diagonal_reduction", "Atlas.LinearGroups.SuzukiFamily.TensorDiagonal", "theorem"), ("Atlas.SuzukiFamily.tensor_matrix_diagonal_reduction", "Atlas.LinearGroups.SuzukiFamily.TensorDiagonal", "theorem"), ("Atlas.SuzukiFamily.tensor_pair_normalization", "Atlas.LinearGroups.SuzukiFamily.TensorAction", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "/home/gerald/atlas/claude/release-update-v1.2-20261030/verification-runs/20261030T092019-audit-batch-batch-002-large-ree"
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
