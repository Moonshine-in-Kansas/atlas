import Atlas.Comparisons
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Comparisons.Catalogue.Entry", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.Extension", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.FieldOfChar", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.FiniteField", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.Fixed", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.Fixed.Model", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.Fixed.card", "Atlas.Comparisons.CatalogueCardinality", "theorem"), ("Atlas.Comparisons.Catalogue.Fixed.label", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.Model", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.admissible", "Atlas.Comparisons.CatalogueModels", "theorem"), ("Atlas.Comparisons.Catalogue.card", "Atlas.Comparisons.CatalogueCardinality", "theorem"), ("Atlas.Comparisons.Catalogue.exceptional_not_isomorphic", "Atlas.Comparisons.CatalogueObstructions", "theorem"), ("Atlas.Comparisons.Catalogue.exists_normalized", "Atlas.Comparisons.CatalogueNormalization", "theorem"), ("Atlas.Comparisons.Catalogue.isomorphic_iff_normalized_label_eq", "Atlas.Comparisons", "theorem"), ("Atlas.Comparisons.Catalogue.isomorphic_of_normalized_label_eq", "Atlas.Comparisons", "theorem"), ("Atlas.Comparisons.Catalogue.label", "Atlas.Comparisons.CatalogueModels", "any"), ("Atlas.Comparisons.Catalogue.normalizeEquiv", "Atlas.Comparisons.CatalogueNormalization", "any"), ("Atlas.Comparisons.Catalogue.normalizedEntry", "Atlas.Comparisons.CatalogueNormalization", "any"), ("Atlas.Comparisons.Catalogue.normalizedEntry_label", "Atlas.Comparisons.CatalogueNormalization", "theorem"), ("Atlas.Comparisons.Catalogue.normalized_label_eq_of_isomorphic", "Atlas.Comparisons", "theorem"), ("Atlas.Comparisons.Catalogue.not_isomorphic_of_normalized_label_ne", "Atlas.Comparisons", "theorem"), ("Atlas.Comparisons.Catalogue.not_isomorphic_of_not_collision", "Atlas.Comparisons.CatalogueCardinality", "theorem"), ("Atlas.Comparisons.Catalogue.same_label_equiv", "Atlas.Comparisons.CatalogueSameLabel", "theorem"), ("Atlas.Comparisons.CatalogueOrders.B_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Co1_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Co2_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Co3_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Dminus_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Dplus_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.F4_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Fi22_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Fi23_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Fi24prime_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.G2_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.HS_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.J2_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.M11_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.M12_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.M22_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.M23_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.M24_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.McL_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Ru_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Suz_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.Tits_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.alternating_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.cyclic_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.field_card_primePower", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.linear_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.smallRee_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.suzuki_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.symplectic_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.triality_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.CatalogueOrders.unitary_card", "Atlas.Comparisons.CatalogueOrders", "theorem"), ("Atlas.Comparisons.SameFieldSize.fieldEquiv", "Atlas.Comparisons.SameFieldSize", "any"), ("Atlas.Comparisons.SameFieldSize.minusEquiv", "Atlas.Comparisons.SameFieldSize", "any"), ("Atlas.Comparisons.SameFieldSize.trialityEquiv", "Atlas.Comparisons.SameFieldSize", "any"), ("Atlas.Comparisons.not_isomorphic_of_card_ne", "Atlas.Comparisons.Cardinality", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019"
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
