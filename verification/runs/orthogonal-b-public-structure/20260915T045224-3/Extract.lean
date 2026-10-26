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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Orthogonal.B1_five_simple", "Atlas.LinearGroups.Orthogonal.BAllRanksChecks", "theorem"), ("Atlas.Orthogonal.B1_three_not_simple", "Atlas.LinearGroups.Orthogonal.BAllRanksChecks", "theorem"), ("Atlas.Orthogonal.B1_three_order", "Atlas.LinearGroups.Orthogonal.BAllRanksChecks", "theorem"), ("Atlas.Orthogonal.B1_two_not_simple", "Atlas.LinearGroups.Orthogonal.BAllRanksChecks", "theorem"), ("Atlas.Orthogonal.B1_two_order", "Atlas.LinearGroups.Orthogonal.BAllRanksChecks", "theorem"), ("Atlas.Orthogonal.B_center_eq_bot", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_center_order", "Atlas.LinearGroups.Orthogonal.BStructure", "theorem"), ("Atlas.Orthogonal.B_elementaryEquiv", "Atlas.LinearGroups.Orthogonal.BConstruction", "any"), ("Atlas.Orthogonal.B_elementaryEquiv_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "any"), ("Atlas.Orthogonal.B_elementary_card_mul_denominator", "Atlas.LinearGroups.Orthogonal.BStructure", "theorem"), ("Atlas.Orthogonal.B_elementary_eq_derived", "Atlas.LinearGroups.Orthogonal.BStructure", "theorem"), ("Atlas.Orthogonal.B_elementary_index", "Atlas.LinearGroups.Orthogonal.BStructure", "theorem"), ("Atlas.Orthogonal.B_elementary_order", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_elementary_order_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.Orthogonal.B_elementary_perfect", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_elementary_perfect_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.Orthogonal.B_equiv_of_card_eq", "Atlas.LinearGroups.Orthogonal.BFamilyTransport", "theorem"), ("Atlas.Orthogonal.B_even_intrinsic", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_faithful", "Atlas.LinearGroups.Orthogonal.BGeometryInterface", "theorem"), ("Atlas.Orthogonal.B_fieldEquiv", "Atlas.LinearGroups.Orthogonal.BConstruction", "any"), ("Atlas.Orthogonal.B_fieldEquiv_projection", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_fieldEquiv_refl", "Atlas.LinearGroups.Orthogonal.BFamilyTransport", "theorem"), ("Atlas.Orthogonal.B_fieldEquiv_symm", "Atlas.LinearGroups.Orthogonal.BFamilyTransport", "theorem"), ("Atlas.Orthogonal.B_fieldEquiv_trans", "Atlas.LinearGroups.Orthogonal.BFamilyTransport", "theorem"), ("Atlas.Orthogonal.B_generated_by_siegel", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_noncommutative", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_noncommutative_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.Orthogonal.B_odd_elementary_primitive", "Atlas.LinearGroups.Orthogonal.BGeometryInterface", "theorem"), ("Atlas.Orthogonal.B_odd_intrinsic", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_odd_roots_normal_generate", "Atlas.LinearGroups.Orthogonal.BGeometryInterface", "theorem"), ("Atlas.Orthogonal.B_odd_transitive", "Atlas.LinearGroups.Orthogonal.BGeometryInterface", "theorem"), ("Atlas.Orthogonal.B_perfect", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_perfect_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.Orthogonal.B_roots_abelian", "Atlas.LinearGroups.Orthogonal.BGeometryInterface", "theorem"), ("Atlas.Orthogonal.B_roots_normal_in_stabilizer", "Atlas.LinearGroups.Orthogonal.BGeometryInterface", "theorem"), ("Atlas.Orthogonal.B_scalar_eq_bot", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_scalar_eq_bot_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.Orthogonal.B_scalar_order", "Atlas.LinearGroups.Orthogonal.BStructure", "theorem"), ("Atlas.Orthogonal.B_simple", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_simple_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.Orthogonal.B_simple_iff", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.Orthogonal.B_simple_iff_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.Orthogonal.card_elementaryB_one_eq_oddKernel", "Atlas.LinearGroups.Orthogonal.B1Structure", "theorem"), ("Atlas.Orthogonal.elementaryB_one_center_eq_bot", "Atlas.LinearGroups.Orthogonal.B1Structure", "theorem"), ("Atlas.Orthogonal.elementaryB_one_eq_intrinsicKernel", "Atlas.LinearGroups.Orthogonal.B1Structure", "theorem"), ("Atlas.Orthogonal.elementaryB_one_kernelEquiv", "Atlas.LinearGroups.Orthogonal.B1Structure", "any"), ("Atlas.Orthogonal.elementaryB_one_to_oddKernel", "Atlas.LinearGroups.Orthogonal.B1Structure", "any"), ("Atlas.Orthogonal.elementaryB_one_to_oddKernel_injective", "Atlas.LinearGroups.Orthogonal.B1Structure", "theorem"), ("Atlas.Orthogonal.elementaryB_one_to_oddKernel_surjective", "Atlas.LinearGroups.Orthogonal.B1Structure", "theorem"), ("Atlas.Orthogonal.fieldEquivElementaryB_refl", "Atlas.LinearGroups.Orthogonal.BFamilyTransport", "theorem"), ("Atlas.Orthogonal.fieldEquivElementaryB_trans", "Atlas.LinearGroups.Orthogonal.BFamilyTransport", "theorem"), ("Atlas.Orthogonal.psl_two_center_eq_bot", "Atlas.LinearGroups.Orthogonal.B1Structure", "theorem"), ("Atlas.exists_typeB", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.exists_typeB_all_ranks", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.typeB_all_ranks_construction", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.typeB_construction", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.typeB_prime_power", "Atlas.LinearGroups.Orthogonal.BConstruction", "theorem"), ("Atlas.typeB_prime_power_all_ranks", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/orthogonal-b-public-structure/20260915T045224-3"
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
