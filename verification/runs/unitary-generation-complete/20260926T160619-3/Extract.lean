import Atlas.LinearGroups.Unitary.BinaryField
import Atlas.LinearGroups.Unitary.BinaryFourBridge
import Atlas.LinearGroups.Unitary.BinaryNormOneTransport
import Atlas.LinearGroups.Unitary.BinaryTwoGeneration
import Atlas.LinearGroups.Unitary.BinaryThreeDenseTransport
import Atlas.LinearGroups.Unitary.BinaryFourGeneration
import Atlas.LinearGroups.Unitary.FourCompression
import Atlas.LinearGroups.Unitary.SupportFourReduction
import Atlas.LinearGroups.Unitary.GeneratedFourTransport
import Atlas.LinearGroups.Unitary.GenerationFourLift
import Atlas.LinearGroups.Unitary.RankOneGeneration
import Atlas.LinearGroups.Unitary.Family
import Atlas.LinearGroups.Unitary.RankOneGenerationAll
import Atlas.LinearGroups.Unitary.GenerationComplete
import Atlas.LinearGroups.Unitary.ThreeRootGroup
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Unitary.binaryBridgeElement", "Atlas.LinearGroups.Unitary.BinaryFourBridge", "any"), ("Atlas.Unitary.binaryBridgeElement_generated", "Atlas.LinearGroups.Unitary.BinaryFourBridge", "any"), ("Atlas.Unitary.binaryBridgeElement_matrix", "Atlas.LinearGroups.Unitary.BinaryFourBridge", "any"), ("Atlas.Unitary.binaryBridgeVector", "Atlas.LinearGroups.Unitary.BinaryFourBridge", "any"), ("Atlas.Unitary.binaryBridge_isotropic", "Atlas.LinearGroups.Unitary.BinaryFourBridge", "any"), ("Atlas.Unitary.binaryBridge_word", "Atlas.LinearGroups.Unitary.BinaryFourBridge", "any"), ("Atlas.Unitary.binaryFourierThree", "Atlas.LinearGroups.Unitary.BinaryFourBridge", "any"), ("Atlas.Unitary.binary_charP", "Atlas.LinearGroups.Unitary.BinaryField", "any"), ("Atlas.Unitary.binary_dense_complement_transport", "Atlas.LinearGroups.Unitary.BinaryThreeDenseTransport", "any"), ("Atlas.Unitary.binary_even_generated_map_to_first", "Atlas.LinearGroups.Unitary.BinaryNormOneTransport", "any"), ("Atlas.Unitary.binary_firstStabilizer_le_generated_of_transport", "Atlas.LinearGroups.Unitary.BinaryFourGeneration", "any"), ("Atlas.Unitary.binary_four_generation_of_dense", "Atlas.LinearGroups.Unitary.BinaryFourGeneration", "any"), ("Atlas.Unitary.binary_hermitian_support_sum", "Atlas.LinearGroups.Unitary.BinaryField", "any"), ("Atlas.Unitary.binary_nonzero_cube", "Atlas.LinearGroups.Unitary.BinaryField", "any"), ("Atlas.Unitary.binary_nonzero_norm", "Atlas.LinearGroups.Unitary.BinaryField", "any"), ("Atlas.Unitary.binary_norm_entry", "Atlas.LinearGroups.Unitary.BinaryField", "any"), ("Atlas.Unitary.binary_norm_one_zero_coordinate", "Atlas.LinearGroups.Unitary.BinaryNormOneTransport", "any"), ("Atlas.Unitary.binary_pow_four", "Atlas.LinearGroups.Unitary.BinaryField", "any"), ("Atlas.Unitary.binary_three_extended_transport_of_dense", "Atlas.LinearGroups.Unitary.BinaryFourGeneration", "any"), ("Atlas.Unitary.binary_transvectionGenerated_four_eq_top", "Atlas.LinearGroups.Unitary.BinaryFourGeneration", "any"), ("Atlas.Unitary.binary_transvectionGenerated_two_eq_top", "Atlas.LinearGroups.Unitary.BinaryTwoGeneration", "any"), ("Atlas.Unitary.charTwo_generated_map_to_first_of_zero", "Atlas.LinearGroups.Unitary.BinaryNormOneTransport", "any"), ("Atlas.Unitary.charTwo_generated_swap_orthogonal", "Atlas.LinearGroups.Unitary.BinaryNormOneTransport", "any"), ("Atlas.Unitary.exists_binary_primitive", "Atlas.LinearGroups.Unitary.BinaryField", "any"), ("Atlas.Unitary.exists_generated_map_sparse_to_first_four", "Atlas.LinearGroups.Unitary.GeneratedFourTransport", "any"), ("Atlas.Unitary.exists_generated_map_to_first_four", "Atlas.LinearGroups.Unitary.GeneratedFourTransport", "any"), ("Atlas.Unitary.exists_generated_reduce_support_four", "Atlas.LinearGroups.Unitary.SupportFourReduction", "any"), ("Atlas.Unitary.exists_generated_sparse_four", "Atlas.LinearGroups.Unitary.SupportFourReduction", "any"), ("Atlas.Unitary.exists_special_compress_four", "Atlas.LinearGroups.Unitary.FourCompression", "any"), ("Atlas.Unitary.special_one_eq_one", "Atlas.LinearGroups.Unitary.BinaryTwoGeneration", "any"), ("Atlas.Unitary.special_two_perfect", "Atlas.LinearGroups.Unitary.RankOneGeneration", "any"), ("Atlas.Unitary.transvectionGenerated_add_four_eq_top_of_four", "Atlas.LinearGroups.Unitary.GenerationFourLift", "any"), ("Atlas.Unitary.transvectionGenerated_eq_top_of_four", "Atlas.LinearGroups.Unitary.GenerationFourLift", "any"), ("Atlas.Unitary.transvectionGenerated_eq_top_of_good", "Atlas.LinearGroups.Unitary.Family", "theorem"), ("Atlas.Unitary.transvectionGenerated_eq_top_of_not_three_binary", "Atlas.LinearGroups.Unitary.GenerationComplete", "theorem"), ("Atlas.Unitary.transvectionGenerated_one_eq_top", "Atlas.LinearGroups.Unitary.BinaryTwoGeneration", "any"), ("Atlas.Unitary.transvectionGenerated_two_eq_top", "Atlas.LinearGroups.Unitary.RankOneGenerationAll", "theorem"), ("Atlas.Unitary.transvectionGenerated_two_eq_top_of_four_le", "Atlas.LinearGroups.Unitary.RankOneGeneration", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/unitary-generation-complete/20260926T160619-3"
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
