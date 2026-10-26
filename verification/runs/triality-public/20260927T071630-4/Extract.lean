import Atlas.LinearGroups.Triality.ParabolicIndices
import Atlas.LinearGroups.Triality.Checks
import Atlas.LinearGroups.Type3D4
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Triality.Group", "Atlas.LinearGroups.Triality.FoldedGenerators", "any"), ("Atlas.Triality.PrimePowerModel", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.Triality.baseFieldEquiv", "Atlas.LinearGroups.Triality.CubicFieldTransport", "any"), ("Atlas.Triality.borelProjection_kernel", "Atlas.LinearGroups.Triality.SplitBorel", "any"), ("Atlas.Triality.borelProjection_section", "Atlas.LinearGroups.Triality.SplitBorel", "any"), ("Atlas.Triality.card_group", "Atlas.LinearGroups.Triality.Order", "any"), ("Atlas.Triality.card_parabolicPoints", "Atlas.LinearGroups.Triality.ParabolicIndices", "any"), ("Atlas.Triality.card_shortParabolicQuotient", "Atlas.LinearGroups.Triality.ParabolicIndices", "any"), ("Atlas.Triality.cellEquiv", "Atlas.LinearGroups.Triality.BruhatNormalForm", "any"), ("Atlas.Triality.compatibleCubicEquiv_exists", "Atlas.LinearGroups.Triality.CubicFieldTransport", "any"), ("Atlas.Triality.dihedralWeylEquiv", "Atlas.LinearGroups.Triality.WeylDihedral", "any"), ("Atlas.Triality.extension_card_q2", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.extension_card_q3", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.extension_card_q4", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.finite_group", "Atlas.LinearGroups.Triality.FoldedGenerators", "any"), ("Atlas.Triality.intoProjective_injective", "Atlas.LinearGroups.Triality.ProjectiveEmbedding", "any"), ("Atlas.Triality.noncommutative", "Atlas.LinearGroups.Triality.Perfect", "any"), ("Atlas.Triality.noncommutative_q2", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.noncommutative_q3", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.noncommutative_q4", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.order_q2", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.order_q3", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.order_q4", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.parabolicPointsEquiv_smul", "Atlas.LinearGroups.Triality.ActionTransport", "any"), ("Atlas.Triality.perfect", "Atlas.LinearGroups.Triality.Perfect", "any"), ("Atlas.Triality.primePower_noncommutative", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.Triality.primePower_order", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.Triality.primePower_simple", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.Triality.simple", "Atlas.LinearGroups.Triality.Simplicity", "any"), ("Atlas.Triality.simple_q2", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.simple_q3", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.simple_q4", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.unipotent_card_q2", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.unipotent_card_q3", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Triality.unipotent_card_q4", "Atlas.LinearGroups.Triality.Checks", "any"), ("Atlas.Type3D4Construction", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.exists_type3D4", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.exists_type3D4_parameter", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.type3D4_construction", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.type3D4_field_transport", "Atlas.LinearGroups.Type3D4", "any"), ("Atlas.type3D4_prime_power", "Atlas.LinearGroups.Type3D4", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/triality-public/20260927T071630-4"
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
