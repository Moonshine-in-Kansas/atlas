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
  let rootSpecs : Array (String × String × String) := #[("Atlas.G2.SimplicityChecks.binary_noncommutative", "Atlas.LinearGroups.G2.SimplicityChecks", "any"), ("Atlas.G2.SimplicityChecks.eight_simple", "Atlas.LinearGroups.G2.SimplicityChecks", "any"), ("Atlas.G2.SimplicityChecks.five_simple", "Atlas.LinearGroups.G2.SimplicityChecks", "any"), ("Atlas.G2.SimplicityChecks.four_simple", "Atlas.LinearGroups.G2.SimplicityChecks", "any"), ("Atlas.G2.SimplicityChecks.ternary_noncommutative", "Atlas.LinearGroups.G2.SimplicityChecks", "any"), ("Atlas.G2.SimplicityChecks.ternary_simple", "Atlas.LinearGroups.G2.SimplicityChecks", "any"), ("Atlas.G2.card_localAt", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.card_longRootLocal", "Atlas.LinearGroups.G2.LongRootLocal", "any"), ("Atlas.G2.conjugate_local_eq", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.isPerfect", "Atlas.LinearGroups.G2.Perfectness", "any"), ("Atlas.G2.isSimple", "Atlas.LinearGroups.G2.Simplicity", "any"), ("Atlas.G2.iwasawa", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.localAt", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.localAtEquiv", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.localAt_commutative", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.localAt_conj", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.localAt_eq_of_transport", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.localAt_first", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.localAt_iSup_eq_normalClosure", "Atlas.LinearGroups.G2.IwasawaLocal", "any"), ("Atlas.G2.longRootLocal", "Atlas.LinearGroups.G2.LongRootLocal", "any"), ("Atlas.G2.longRootLocal_commutative", "Atlas.LinearGroups.G2.LongRootLocal", "any"), ("Atlas.G2.longRootLocal_normal_in_pointStabilizer", "Atlas.LinearGroups.G2.LocalNormalizer", "any"), ("Atlas.G2.longRootNormalClosure", "Atlas.LinearGroups.G2.LongRootNormalGeneration", "any"), ("Atlas.G2.longRootNormalClosure_eq_top", "Atlas.LinearGroups.G2.LongRootNormalGeneration", "any"), ("Atlas.G2.longRootParameterEquiv", "Atlas.LinearGroups.G2.LongRootLocal", "any"), ("Atlas.G2.normal_eq_top_of_unipotent", "Atlas.LinearGroups.G2.LongRootNormalGeneration", "any"), ("Atlas.G2.pointStabilizer_le_longRootNormalizer", "Atlas.LinearGroups.G2.LocalNormalizer", "any"), ("Atlas.G2.rootA_mem_commutator", "Atlas.LinearGroups.G2.Perfectness", "any"), ("Atlas.G2.unipotent_le_longRootNormalClosure", "Atlas.LinearGroups.G2.LongRootNormalGeneration", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/g2-simplicity/20260916T032150-3"
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
