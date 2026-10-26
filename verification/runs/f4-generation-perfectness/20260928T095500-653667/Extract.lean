import Atlas.LinearGroups.F4.TorusLongRootMaps
import Atlas.LinearGroups.F4.TorusLongRootBridge
import Atlas.LinearGroups.F4.TorusShortRootMaps
import Atlas.LinearGroups.F4.SimpleCorootDefinitions
import Atlas.LinearGroups.F4.ShortRootPairTwo
import Atlas.LinearGroups.F4.SimpleCorootActions
import Atlas.LinearGroups.F4.SimpleCoroots
import Atlas.LinearGroups.F4.TorusWeylWords
import Atlas.LinearGroups.F4.TorusRootWords
import Atlas.LinearGroups.F4.TorusGenerated
import Atlas.LinearGroups.F4.LeviGeneratedImage
import Atlas.LinearGroups.F4.Generation
import Atlas.LinearGroups.F4.Perfect
import Atlas.LinearGroups.F4.RadicalNormalClosure
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.F4.albertMapAddHom", "Atlas.LinearGroups.F4.TorusLongRootMaps", "any"), ("Atlas.F4.diagonalTorus_mem_rootGenerated", "Atlas.LinearGroups.F4.TorusGenerated", "theorem"), ("Atlas.F4.elementaryB3_le_generatedLeviImage", "Atlas.LinearGroups.F4.LeviGeneratedImage", "theorem"), ("Atlas.F4.generatedLeviImage", "Atlas.LinearGroups.F4.LeviGeneratedImage", "any"), ("Atlas.F4.generatedParabolic", "Atlas.LinearGroups.F4.LeviGeneratedImage", "any"), ("Atlas.F4.generated_eq_top", "Atlas.LinearGroups.F4.Generation", "theorem"), ("Atlas.F4.isPerfect", "Atlas.LinearGroups.F4.Perfect", "theorem"), ("Atlas.F4.leviDiagonal_mem_generatedLeviImage", "Atlas.LinearGroups.F4.LeviGeneratedImage", "theorem"), ("Atlas.F4.leviLongRoot_mem_generatedParabolic", "Atlas.LinearGroups.F4.LeviGeneratedImage", "theorem"), ("Atlas.F4.leviShortRoot_mem_generatedParabolic", "Atlas.LinearGroups.F4.LeviGeneratedImage", "theorem"), ("Atlas.F4.longRoot_torusLongApply", "Atlas.LinearGroups.F4.TorusLongRootBridge", "theorem"), ("Atlas.F4.normal_eq_top_of_contains_radical", "Atlas.LinearGroups.F4.Perfect", "theorem"), ("Atlas.F4.parabolicKernel_mem_rootGenerated", "Atlas.LinearGroups.F4.Generation", "theorem"), ("Atlas.F4.parabolic_le_rootGenerated", "Atlas.LinearGroups.F4.Generation", "theorem"), ("Atlas.F4.radical_normalClosure_eq_top", "Atlas.LinearGroups.F4.RadicalNormalClosure", "theorem"), ("Atlas.F4.radical_normal_in_pointStabilizer", "Atlas.LinearGroups.F4.RadicalNormalClosure", "theorem"), ("Atlas.F4.shortRootLinear_torusShortApply3", "Atlas.LinearGroups.F4.TorusShortRootMaps", "theorem"), ("Atlas.F4.shortRootLinear_torusShortApply4", "Atlas.LinearGroups.F4.TorusShortRootMaps", "theorem"), ("Atlas.F4.shortRoot_pair_two_apply", "Atlas.LinearGroups.F4.ShortRootPairTwo", "theorem"), ("Atlas.F4.simpleCorootParameters", "Atlas.LinearGroups.F4.SimpleCorootDefinitions", "any"), ("Atlas.F4.simpleCorootWord", "Atlas.LinearGroups.F4.SimpleCorootDefinitions", "any"), ("Atlas.F4.simpleCorootWord_eq_diagonalTorus", "Atlas.LinearGroups.F4.TorusRootWords", "theorem"), ("Atlas.F4.simpleCorootWord_mem_rootGenerated", "Atlas.LinearGroups.F4.SimpleCoroots", "theorem"), ("Atlas.F4.simpleCoroot_mem_rootGenerated", "Atlas.LinearGroups.F4.TorusRootWords", "theorem"), ("Atlas.F4.simpleNegative", "Atlas.LinearGroups.F4.SimpleCorootDefinitions", "any"), ("Atlas.F4.simpleNegativeApply", "Atlas.LinearGroups.F4.SimpleCorootDefinitions", "any"), ("Atlas.F4.simpleNegative_add", "Atlas.LinearGroups.F4.SimpleCoroots", "theorem"), ("Atlas.F4.simpleNegative_apply", "Atlas.LinearGroups.F4.SimpleCorootActions", "theorem"), ("Atlas.F4.simpleNegative_mem_rootGenerated", "Atlas.LinearGroups.F4.SimpleCoroots", "theorem"), ("Atlas.F4.simpleNegative_zero", "Atlas.LinearGroups.F4.SimpleCoroots", "theorem"), ("Atlas.F4.simplePositive", "Atlas.LinearGroups.F4.SimpleCorootDefinitions", "any"), ("Atlas.F4.simplePositiveApply", "Atlas.LinearGroups.F4.SimpleCorootDefinitions", "any"), ("Atlas.F4.simplePositive_add", "Atlas.LinearGroups.F4.SimpleCoroots", "theorem"), ("Atlas.F4.simplePositive_apply", "Atlas.LinearGroups.F4.SimpleCorootActions", "theorem"), ("Atlas.F4.simplePositive_mem_rootGenerated", "Atlas.LinearGroups.F4.SimpleCoroots", "theorem"), ("Atlas.F4.simplePositive_zero", "Atlas.LinearGroups.F4.SimpleCoroots", "theorem"), ("Atlas.F4.simpleWeyl_factorization", "Atlas.LinearGroups.F4.TorusWeylWords", "theorem"), ("Atlas.F4.specialB3_le_generatedLeviImage", "Atlas.LinearGroups.F4.LeviGeneratedImage", "theorem"), ("Atlas.F4.torusCorootPreimage", "Atlas.LinearGroups.F4.TorusGenerated", "any"), ("Atlas.F4.torusCorootPreimage_identity", "Atlas.LinearGroups.F4.TorusGenerated", "theorem"), ("Atlas.F4.torusLongApply", "Atlas.LinearGroups.F4.TorusLongRootMaps", "any"), ("Atlas.F4.torusLongApply_map", "Atlas.LinearGroups.F4.TorusLongRootMaps", "theorem"), ("Atlas.F4.torusLongApply_parameter", "Atlas.LinearGroups.F4.TorusLongRootMaps", "theorem"), ("Atlas.F4.torusLongLabel", "Atlas.LinearGroups.F4.TorusLongRootMaps", "any"), ("Atlas.F4.torusLongLinear", "Atlas.LinearGroups.F4.TorusLongRootMaps", "any"), ("Atlas.F4.torusLongSeedColumn", "Atlas.LinearGroups.F4.TorusLongRootMaps", "any"), ("Atlas.F4.torusLong_columns", "Atlas.LinearGroups.F4.TorusLongRootMaps", "theorem"), ("Atlas.F4.torusLong_integral_columns", "Atlas.LinearGroups.F4.TorusLongRootMaps", "theorem"), ("Atlas.F4.torusShortApply3", "Atlas.LinearGroups.F4.TorusShortRootMaps", "any"), ("Atlas.F4.torusShortApply4", "Atlas.LinearGroups.F4.TorusShortRootMaps", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/f4-generation-perfectness/20260928T095500-653667"
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
