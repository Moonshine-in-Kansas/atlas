import Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder
import Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors
import Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction
import Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Chevalley.TwistedE6.TorusUnitParameters.Parameters", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "definition"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.conjugationUnits_conjugationUnits", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.conjugationUnits_embedUnits", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.conjugationUnits_fixed_iff", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.conjugationUnits_involutive", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.conjugationUnits_val", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.embedUnits", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "definition"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.embedUnits_injective", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.embedUnits_val", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.expand", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "definition"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.expand_mem", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.fixedUnitTuples", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "definition"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.fixedUnitTuples_card", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.mem_fixedUnitTuples", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parameterHom", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "definition"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parameterHom_injective", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parameterHom_surjective", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parameterHom_val", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parametersEquiv", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "definition"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parametersEquiv_symm_base", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parametersEquiv_symm_extension", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parametersEquiv_val", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.TorusUnitParameters.parameters_card", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters", "theorem"), ("Atlas.Chevalley.TwistedE6.companionDiagram_e6PublicTorusParameters", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.companionDiagram_e6SimpleTorus", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem"), ("Atlas.Chevalley.TwistedE6.companionDiagram_e6SimpleWeylUnit", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem"), ("Atlas.Chevalley.TwistedE6.companionFixedTorus", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "definition"), ("Atlas.Chevalley.TwistedE6.companionFixedTorusParametersEquiv", "Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder", "definition"), ("Atlas.Chevalley.TwistedE6.companionFixedTorusParametersEquiv_val", "Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder", "theorem"), ("Atlas.Chevalley.TwistedE6.companionFixedTorus_card", "Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder", "theorem"), ("Atlas.Chevalley.TwistedE6.companionFrobenius_e6PublicTorusParameters", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.companionFrobenius_e6SimpleTorus", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem"), ("Atlas.Chevalley.TwistedE6.companionFrobenius_e6SimpleWeylUnit", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem"), ("Atlas.Chevalley.TwistedE6.companionTwist_e6PublicTorusParameters", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.companionTwist_e6SimpleTorus", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem"), ("Atlas.Chevalley.TwistedE6.conjugationUnits", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "definition"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParameters", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "definition"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParametersEquiv", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "definition"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParametersEquiv_mem_companionFixedSubgroup_iff", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParametersEquiv_val", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParameters_apply", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParameters_injective", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParameters_mem", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParameters_mem_companionFixedSubgroup_iff", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParameters_mem_companionFixedTorus_iff", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusParameters_mulSingle", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusReindex", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "definition"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusReindex_apply", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6PublicTorusReindex_mulSingle", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6SimpleTorus", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "definition"), ("Atlas.Chevalley.TwistedE6.e6SimpleTorus_eq_inherited", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem"), ("Atlas.Chevalley.TwistedE6.e6SimpleWeylUnit", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "definition"), ("Atlas.Chevalley.TwistedE6.e6TorusParametersEquiv", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "definition"), ("Atlas.Chevalley.TwistedE6.e6TorusParameters_single", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem"), ("Atlas.Chevalley.TwistedE6.e6TorusSubgroup_eq_range", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem"), ("Atlas.Chevalley.TwistedE6.e6TorusTupleDiagram", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "definition"), ("Atlas.Chevalley.TwistedE6.e6TorusTupleDiagram_apply", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6TorusTupleDiagram_mulSingle", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6TorusTupleFrobenius", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "definition"), ("Atlas.Chevalley.TwistedE6.e6TorusTupleFrobenius_apply", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.e6TorusTupleFrobenius_mulSingle", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction", "theorem"), ("Atlas.Chevalley.TwistedE6.fixedTorusTupleEquiv", "Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder", "definition"), ("Atlas.Chevalley.TwistedE6.fixedTorusTupleHom", "Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder", "definition"), ("Atlas.Chevalley.TwistedE6.fixedTorusTupleHom_injective", "Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder", "theorem"), ("Atlas.Chevalley.TwistedE6.fixedTorusTupleHom_surjective", "Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder", "theorem"), ("Atlas.Chevalley.TwistedE6.fixedTorusTupleHom_val", "Atlas.LinearGroups.Chevalley.TwistedE6.FixedTorusOrder", "theorem"), ("Atlas.Chevalley.TwistedE6.mem_companionFixedTorus_iff", "Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "/home/gerald/atlas/claude/release-update-v1.2-20261030/verification-runs/20261030T092307-audit-batch-batch-003-twisted-e6"
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
