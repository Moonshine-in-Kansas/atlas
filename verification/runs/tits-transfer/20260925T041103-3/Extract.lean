import Atlas.Tits.FiveQuartetImageOrder
import Atlas.Tits.FiveQuartetMultiplier
import Atlas.Tits.FiveQuartetMultiplierProperties
import Atlas.Tits.TransferDefinition
import Atlas.Tits.TransferWitnessPowers
import Atlas.Tits.TransferWitnessCycles
import Atlas.Tits.TransferFixedCharacters
import Atlas.Tits.TransferGeometricProduct
import Atlas.Tits.TransferTwoCycleCancellation
import Atlas.Tits.TransferEvaluation
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Tits.alphaCycleValue_row_constant", "Atlas.Tits.TransferTwoCycleCancellation", "theorem"), ("Atlas.Tits.alphaCycleValue_two_square", "Atlas.Tits.TransferTwoCycleCancellation", "theorem"), ("Atlas.Tits.alphaFixedNeighbour_coordinate", "Atlas.Tits.TransferFixedCharacters", "theorem"), ("Atlas.Tits.alphaFixedNeighbour_exhaustion", "Atlas.Tits.TransferFixedCharacters", "theorem"), ("Atlas.Tits.alphaFixedNeighbour_injective", "Atlas.Tits.TransferFixedCharacters", "theorem"), ("Atlas.Tits.alphaTranslationMatrix_columns", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.alphaTranslationMatrix_point_trace", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.alphaTranslationMatrix_sum", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.alphaTwoCycleRow_spec", "Atlas.Tits.TransferTwoCycleCancellation", "theorem"), ("Atlas.Tits.alpha_coordinate_fixed_certificate", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.alpha_cycle_length_cases", "Atlas.Tits.TransferEvaluation", "theorem"), ("Atlas.Tits.alpha_four_cycle_value", "Atlas.Tits.TransferEvaluation", "theorem"), ("Atlas.Tits.alpha_nonfixed_cycle_product", "Atlas.Tits.TransferEvaluation", "theorem"), ("Atlas.Tits.alpha_one_cycle_product", "Atlas.Tits.TransferEvaluation", "theorem"), ("Atlas.Tits.alpha_one_cycle_value", "Atlas.Tits.TransferEvaluation", "theorem"), ("Atlas.Tits.alpha_row_cycle_product", "Atlas.Tits.TransferTwoCycleCancellation", "theorem"), ("Atlas.Tits.alpha_two_cycle_product", "Atlas.Tits.TransferTwoCycleCancellation", "theorem"), ("Atlas.Tits.codeAlpha_coordinate_fixed_iff", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.fiveQuartetConjugation_stabilizer_injective", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetConjugation_surjective", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetHom_kernel_order", "Atlas.Tits.FiveQuartetMultiplierProperties", "theorem"), ("Atlas.Tits.fiveQuartetImageMultiplier_exponent", "Atlas.Tits.FiveQuartetMultiplierProperties", "theorem"), ("Atlas.Tits.fiveQuartetImageMultiplier_involution", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetImageMultiplier_kernel_order", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetImageMultiplier_surjective", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetImage_card_dvd", "Atlas.Tits.FiveQuartetImageOrder", "theorem"), ("Atlas.Tits.fiveQuartetImage_order", "Atlas.Tits.FiveQuartetImageOrder", "theorem"), ("Atlas.Tits.fiveQuartetImage_point_stabilizer_order", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetMultiplier_generator_independent", "Atlas.Tits.FiveQuartetMultiplierProperties", "theorem"), ("Atlas.Tits.fiveQuartetMultiplier_kernel_order", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetMultiplier_surjective", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetSylow_order", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.fiveQuartetSylow_unique", "Atlas.Tits.FiveQuartetMultiplier", "theorem"), ("Atlas.Tits.geometricCycleLength_eq_period", "Atlas.Tits.TransferEvaluation", "theorem"), ("Atlas.Tits.geometricCycleValue_mk", "Atlas.Tits.TransferGeometricProduct", "theorem"), ("Atlas.Tits.geometricCycleValue_out", "Atlas.Tits.TransferGeometricProduct", "theorem"), ("Atlas.Tits.imageBeta_order", "Atlas.Tits.FiveQuartetImageOrder", "theorem"), ("Atlas.Tits.localAlpha_fixed_card", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_fixed_iff", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_four_cycles_card", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_fourth", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.localAlpha_one_cycles_card", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_period_cases", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_period_four_iff", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_period_four_points_card", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_period_one_iff", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_period_two_iff", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_period_two_points_card", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localAlpha_square", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.localAlpha_two_cycles_card", "Atlas.Tits.TransferWitnessCycles", "theorem"), ("Atlas.Tits.localCodeAlpha_square", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.localCodeAlpha_translation", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.localCodeAlpha_transport", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.multiplierAt_alphaFixedNeighbour", "Atlas.Tits.TransferFixedCharacters", "theorem"), ("Atlas.Tits.multiplierAt_alpha_fixed", "Atlas.Tits.TransferFixedCharacters", "theorem"), ("Atlas.Tits.neighbourCosetEquiv_mk", "Atlas.Tits.TransferDefinition", "theorem"), ("Atlas.Tits.neighbourCosetEquiv_out", "Atlas.Tits.TransferGeometricProduct", "theorem"), ("Atlas.Tits.neighbourCosetEquiv_period", "Atlas.Tits.TransferDefinition", "theorem"), ("Atlas.Tits.neighbourCosetEquiv_smul", "Atlas.Tits.TransferDefinition", "theorem"), ("Atlas.Tits.neighbour_period_same_orbit", "Atlas.Tits.TransferGeometricProduct", "theorem"), ("Atlas.Tits.originalAlpha_square", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.originalE3_square", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.pointAlpha_fourth", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.pointAlpha_square", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.pointCycleValue_orbit", "Atlas.Tits.TransferGeometricProduct", "theorem"), ("Atlas.Tits.pointE3_square", "Atlas.Tits.TransferWitnessPowers", "theorem"), ("Atlas.Tits.transfer", "Atlas.Tits.TransferDefinition", "definition"), ("Atlas.Tits.transfer_alpha", "Atlas.Tits.TransferEvaluation", "theorem"), ("Atlas.Tits.transfer_cycle_product", "Atlas.Tits.TransferDefinition", "theorem"), ("Atlas.Tits.transfer_cycle_product_neighbour_period", "Atlas.Tits.TransferDefinition", "theorem"), ("Atlas.Tits.transfer_geometric_cycle_product", "Atlas.Tits.TransferGeometricProduct", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/tits-transfer/20260925T041103-3"
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
