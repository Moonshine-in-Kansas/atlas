import Atlas.LinearGroups.Type2A
import Atlas.LinearGroups.Unitary.FamilyChecks
import Atlas.LinearGroups.Unitary.Basic
import Atlas.LinearGroups.Unitary.ProjectiveOrder
import Atlas.LinearGroups.Unitary.Family
import Atlas.LinearGroups.Unitary.Projective
import Atlas.LinearGroups.Unitary.IsotropicCount
import Atlas.LinearGroups.Unitary.Center
import Atlas.LinearGroups.Unitary.FixedPoints
import Atlas.LinearGroups.Unitary.BaseFieldTransport
import Atlas.LinearGroups.Unitary.ThreeRootGroup
import Atlas.LinearGroups.Unitary.RankOneGenerationAll
import Atlas.LinearGroups.Unitary.GenerationComplete
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Type2AConstruction", "Atlas.LinearGroups.Type2A", "any"), ("Atlas.Unitary.OrderChecks.points_four_binary", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.points_three_ternary", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.psu_five_binary_simple", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.psu_four_binary_simple", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.psu_four_ternary_simple", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.psu_three_binary_not_simple", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.psu_three_ternary_simple", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.psu_two_binary_not_simple", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.psu_two_quaternary_regression", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.OrderChecks.psu_two_ternary_not_simple", "Atlas.LinearGroups.Unitary.FamilyChecks", "any"), ("Atlas.Unitary.PSU", "Atlas.LinearGroups.Unitary.Basic", "any"), ("Atlas.Unitary.card_center", "Atlas.LinearGroups.Unitary.Center", "any"), ("Atlas.Unitary.card_isotropicPoints", "Atlas.LinearGroups.Unitary.IsotropicCount", "any"), ("Atlas.Unitary.card_psu_factor", "Atlas.LinearGroups.Unitary.ProjectiveOrder", "any"), ("Atlas.Unitary.card_psu_mul_gcd", "Atlas.LinearGroups.Unitary.ProjectiveOrder", "any"), ("Atlas.Unitary.card_threeRootGroup", "Atlas.LinearGroups.Unitary.ThreeRootGroup", "any"), ("Atlas.Unitary.center_eq_scalarSubgroup", "Atlas.LinearGroups.Unitary.Center", "any"), ("Atlas.Unitary.finite_psu", "Atlas.LinearGroups.Unitary.Basic", "any"), ("Atlas.Unitary.graphFieldAutomorphism_involutive", "Atlas.LinearGroups.Unitary.FixedPoints", "any"), ("Atlas.Unitary.isotropic_primitive", "Atlas.LinearGroups.Unitary.Family", "any"), ("Atlas.Unitary.noncommutative_of_good", "Atlas.LinearGroups.Unitary.Family", "any"), ("Atlas.Unitary.projectiveEmbedding_injective", "Atlas.LinearGroups.Unitary.Projective", "any"), ("Atlas.Unitary.projectiveUnitaryEquivOfBaseCardEq", "Atlas.LinearGroups.Unitary.BaseFieldTransport", "any"), ("Atlas.Unitary.simple_iff_good", "Atlas.LinearGroups.Unitary.Family", "any"), ("Atlas.Unitary.simple_of_good", "Atlas.LinearGroups.Unitary.Family", "any"), ("Atlas.Unitary.specialUnitaryFixedEquiv", "Atlas.LinearGroups.Unitary.FixedPoints", "any"), ("Atlas.Unitary.special_perfect_of_good", "Atlas.LinearGroups.Unitary.Family", "any"), ("Atlas.Unitary.threeRootElement_mem_center_iff", "Atlas.LinearGroups.Unitary.ThreeRootGroup", "any"), ("Atlas.Unitary.threeRootGroup", "Atlas.LinearGroups.Unitary.ThreeRootGroup", "any"), ("Atlas.Unitary.threeRootGroup_center_iff", "Atlas.LinearGroups.Unitary.ThreeRootGroup", "any"), ("Atlas.Unitary.threeRootParameterEquiv", "Atlas.LinearGroups.Unitary.ThreeRootGroup", "any"), ("Atlas.Unitary.transvectionGenerated_eq_top_of_good", "Atlas.LinearGroups.Unitary.Family", "any"), ("Atlas.Unitary.transvectionGenerated_eq_top_of_not_three_binary", "Atlas.LinearGroups.Unitary.GenerationComplete", "theorem"), ("Atlas.Unitary.transvectionGenerated_two_eq_top", "Atlas.LinearGroups.Unitary.RankOneGenerationAll", "theorem"), ("Atlas.exists_type2A", "Atlas.LinearGroups.Type2A", "any"), ("Atlas.type2A_construction", "Atlas.LinearGroups.Type2A", "any"), ("Atlas.type2A_prime_power", "Atlas.LinearGroups.Type2A", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/unitary-public/20260926T160854-4"
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
