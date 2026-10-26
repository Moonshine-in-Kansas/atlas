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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Orthogonal.Checks.d4_four_order", "Atlas.LinearGroups.Orthogonal.DOrderChecks", "theorem"), ("Atlas.Orthogonal.Checks.d4_four_simple", "Atlas.LinearGroups.Orthogonal.DSimplicityChecks", "theorem"), ("Atlas.Orthogonal.Checks.d4_three_order", "Atlas.LinearGroups.Orthogonal.DOrderChecks", "theorem"), ("Atlas.Orthogonal.Checks.d4_three_simple", "Atlas.LinearGroups.Orthogonal.DSimplicityChecks", "theorem"), ("Atlas.Orthogonal.DPlus", "Atlas.LinearGroups.Orthogonal.DFamily", "any"), ("Atlas.Orthogonal.DPlus_admissible", "Atlas.LinearGroups.Orthogonal.DFamily", "any"), ("Atlas.Orthogonal.DPlus_card", "Atlas.LinearGroups.Orthogonal.DFamily", "theorem"), ("Atlas.Orthogonal.DPlus_card_mul_denominator", "Atlas.LinearGroups.Orthogonal.DFamily", "theorem"), ("Atlas.Orthogonal.DPlus_center_order", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_center_order_exact", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_elementary_eq_derived", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_elementary_index", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_elementary_order", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_elementary_order_exact", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_elementary_perfect", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_equiv_of_card_eq", "Atlas.LinearGroups.Orthogonal.DFamilyTransport", "theorem"), ("Atlas.Orthogonal.DPlus_even_intrinsic", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_faithful", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_fieldEquiv", "Atlas.LinearGroups.Orthogonal.DFamilyTransport", "any"), ("Atlas.Orthogonal.DPlus_fieldEquiv_projection", "Atlas.LinearGroups.Orthogonal.DFamilyTransport", "theorem"), ("Atlas.Orthogonal.DPlus_fieldEquiv_refl", "Atlas.LinearGroups.Orthogonal.DFamilyTransport", "theorem"), ("Atlas.Orthogonal.DPlus_fieldEquiv_symm", "Atlas.LinearGroups.Orthogonal.DFamilyTransport", "theorem"), ("Atlas.Orthogonal.DPlus_fieldEquiv_trans", "Atlas.LinearGroups.Orthogonal.DFamilyTransport", "theorem"), ("Atlas.Orthogonal.DPlus_finite", "Atlas.LinearGroups.Orthogonal.DFamily", "theorem"), ("Atlas.Orthogonal.DPlus_full_order", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_noncommutative", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_odd_intrinsic", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_order", "Atlas.LinearGroups.Orthogonal.DFamily", "any"), ("Atlas.Orthogonal.DPlus_order_denominator", "Atlas.LinearGroups.Orthogonal.DFamily", "any"), ("Atlas.Orthogonal.DPlus_order_denominator_positive", "Atlas.LinearGroups.Orthogonal.DFamily", "theorem"), ("Atlas.Orthogonal.DPlus_order_divisibility", "Atlas.LinearGroups.Orthogonal.DFamily", "theorem"), ("Atlas.Orthogonal.DPlus_order_numerator", "Atlas.LinearGroups.Orthogonal.DFamily", "any"), ("Atlas.Orthogonal.DPlus_order_numerator_positive", "Atlas.LinearGroups.Orthogonal.DFamily", "theorem"), ("Atlas.Orthogonal.DPlus_perfect", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_primitive", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_roots_normal_generate", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_scalar_eq_center", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_scalar_order_exact", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_simple", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_simple_iff", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_transitive", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Orthogonal.card_elementaryD_all_char", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.card_elementaryD_all_char_mul_gcd_two", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.card_elementaryD_center_all_char", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.card_elementaryD_center_all_char_mul_gcd_two", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.card_elementaryD_scalar_all_char_mul_gcd_two", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.dicksonValue_fieldEquivFullD", "Atlas.LinearGroups.Orthogonal.DicksonValueFieldTransport", "theorem"), ("Atlas.Orthogonal.dicksonValue_semilinear_transport", "Atlas.LinearGroups.Orthogonal.DicksonValueFieldTransport", "theorem"), ("Atlas.Orthogonal.elementaryD_index_all_char", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.elementaryD_scalar_eq_center", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.fieldEquivDicksonKernelD", "Atlas.LinearGroups.Orthogonal.DicksonFieldTransport", "any"), ("Atlas.Orthogonal.fieldEquivDicksonKernelD_elementary", "Atlas.LinearGroups.Orthogonal.DicksonFieldTransport", "theorem"), ("Atlas.Orthogonal.fieldEquivDicksonKernelD_full", "Atlas.LinearGroups.Orthogonal.DicksonFieldTransport", "theorem"), ("Atlas.Orthogonal.fieldEquivDicksonKernelD_projective", "Atlas.LinearGroups.Orthogonal.DicksonFieldTransport", "theorem"), ("Atlas.Orthogonal.fieldEquivElementaryD_refl", "Atlas.LinearGroups.Orthogonal.DFamilyTransport", "theorem"), ("Atlas.Orthogonal.fieldEquivElementaryD_trans", "Atlas.LinearGroups.Orthogonal.DFamilyTransport", "theorem"), ("Atlas.Orthogonal.fullDicksonD_field_transport", "Atlas.LinearGroups.Orthogonal.DicksonValueFieldTransport", "theorem"), ("Atlas.Orthogonal.fullDicksonKernelElementaryEquiv", "Atlas.LinearGroups.Orthogonal.DicksonFieldTransport", "any"), ("Atlas.Orthogonal.orthogonal_gcd_two_even", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.orthogonal_gcd_two_odd", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "theorem"), ("Atlas.Orthogonal.projectiveDQuotientCenterEquiv", "Atlas.LinearGroups.Orthogonal.DStructureAllChar", "any"), ("Atlas.Orthogonal.residual_finrank_fieldEquivFullD", "Atlas.LinearGroups.Orthogonal.DicksonValueFieldTransport", "theorem"), ("Atlas.Orthogonal.residual_finrank_semilinear_transport", "Atlas.LinearGroups.Orthogonal.DicksonValueFieldTransport", "theorem"), ("Atlas.Orthogonal.semilinearResidualEquiv", "Atlas.LinearGroups.Orthogonal.DicksonValueFieldTransport", "any"), ("Atlas.TypeDConstruction", "Atlas.LinearGroups.Orthogonal.DConstruction", "any"), ("Atlas.exists_typeD", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.typeD_construction", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.typeD_prime_power", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/orthogonal-d-family-structure/20260915T032826-3"
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
