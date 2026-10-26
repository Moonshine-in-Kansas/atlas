import Atlas.LinearGroups.TypeReeG2
import Atlas.LinearGroups.ReeG2.Checks
import Atlas.LinearGroups.ReeG2.G2Embedding
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.ReeG2.Checks.action243", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.action27", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.borelOrder243", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.borelOrder27", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.inverseTwist243", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.inverseTwist27", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.nonabelian243", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.nonabelian27", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.order2187", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.order243", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.order27", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.parameters2187", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.pointCount243", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.pointCount27", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.rootOrder243", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.rootOrder27", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.simple243", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Checks.simple27", "Atlas.LinearGroups.ReeG2.Checks", "any"), ("Atlas.ReeG2.Model", "Atlas.LinearGroups.ReeG2.Generators", "any"), ("Atlas.ReeG2.card_borel", "Atlas.LinearGroups.ReeG2.Borel", "any"), ("Atlas.ReeG2.card_pointSet", "Atlas.LinearGroups.ReeG2.Points", "any"), ("Atlas.ReeG2.fieldEquiv", "Atlas.LinearGroups.ReeG2.FieldTransport", "any"), ("Atlas.ReeG2.finite_model", "Atlas.LinearGroups.TypeReeG2", "any"), ("Atlas.ReeG2.fixes_infinity_iff_mem_borel", "Atlas.LinearGroups.ReeG2.ExactStabilizer", "any"), ("Atlas.ReeG2.g2Embedding", "Atlas.LinearGroups.ReeG2.G2Embedding", "any"), ("Atlas.ReeG2.g2Embedding_injective", "Atlas.LinearGroups.ReeG2.G2Embedding", "any"), ("Atlas.ReeG2.infinityStabilizer_eq_borel", "Atlas.LinearGroups.ReeG2.Order", "any"), ("Atlas.ReeG2.model_noncommutative", "Atlas.LinearGroups.ReeG2.Noncommutative", "any"), ("Atlas.ReeG2.order", "Atlas.LinearGroups.ReeG2.Order", "any"), ("Atlas.ReeG2.perfect", "Atlas.LinearGroups.ReeG2.Perfect", "any"), ("Atlas.ReeG2.pointAction_faithful", "Atlas.LinearGroups.ReeG2.FaithfulAction", "any"), ("Atlas.ReeG2.pointAction_preprimitive", "Atlas.LinearGroups.ReeG2.PointTransitivity", "any"), ("Atlas.ReeG2.pointAction_two_pretransitive", "Atlas.LinearGroups.ReeG2.PointTransitivity", "any"), ("Atlas.ReeG2.simple", "Atlas.LinearGroups.ReeG2.Simplicity", "any"), ("Atlas.TypeReeG2Construction", "Atlas.LinearGroups.TypeReeG2", "any"), ("Atlas.exists_typeReeG2", "Atlas.LinearGroups.TypeReeG2", "any"), ("Atlas.exists_typeReeG2_parameter", "Atlas.LinearGroups.TypeReeG2", "any"), ("Atlas.typeReeG2_construction", "Atlas.LinearGroups.TypeReeG2", "any"), ("Atlas.typeReeG2_field_transport", "Atlas.LinearGroups.TypeReeG2", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/ree-g2-family-interface/20260917T051857-3"
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
