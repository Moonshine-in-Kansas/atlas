import Atlas.LinearGroups.ReeF4.ChartLongConjugate0
import Atlas.LinearGroups.ReeF4.ChartLongConjugate1
import Atlas.LinearGroups.ReeF4.ChartLongConjugate2
import Atlas.LinearGroups.ReeF4.ChartLongConjugate3
import Atlas.LinearGroups.ReeF4.ChartPositiveConjugates
import Atlas.LinearGroups.ReeF4.ChartShortConjugate0
import Atlas.LinearGroups.ReeF4.ChartShortConjugate1
import Atlas.LinearGroups.ReeF4.ChartShortConjugate2
import Atlas.LinearGroups.ReeF4.ChartTerminalEndpoints
import Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity
import Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity
import Atlas.LinearGroups.ReeF4.PositiveRootPointAction
import Atlas.LinearGroups.ReeF4.SpecialOppositeAction
import Atlas.LinearGroups.ReeF4.SpecialOppositePairCount
import Atlas.LinearGroups.ReeF4.SpecialOppositePairs
import Atlas.LinearGroups.ReeF4.SpecialOppositePoints
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.ReeF4.AbsoluteUnitriangular.fixes_lowestRoot", "Atlas.LinearGroups.ReeF4.PositiveRootPointAction", "theorem"), ("Atlas.ReeF4.AbsoluteUnitriangular.preserves_highestCoefficient", "Atlas.LinearGroups.ReeF4.PositiveRootPointAction", "theorem"), ("Atlas.ReeF4.OppositeFiber", "Atlas.LinearGroups.ReeF4.SpecialOppositePairCount", "definition"), ("Atlas.ReeF4.OppositeSpecialPoints", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "definition"), ("Atlas.ReeF4.SpecialOpposite", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "definition"), ("Atlas.ReeF4.SpecialOppositePairs", "Atlas.LinearGroups.ReeF4.SpecialOppositePairs", "definition"), ("Atlas.ReeF4.baseSpecialOppositePair", "Atlas.LinearGroups.ReeF4.SpecialOppositePairs", "definition"), ("Atlas.ReeF4.card_oppositeFiber", "Atlas.LinearGroups.ReeF4.SpecialOppositePairCount", "theorem"), ("Atlas.ReeF4.card_oppositeSpecialPoints", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.card_specialOppositePairs", "Atlas.LinearGroups.ReeF4.SpecialOppositePairCount", "theorem"), ("Atlas.ReeF4.carrierConjugate", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "definition"), ("Atlas.ReeF4.chart9ToOpposite", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "definition"), ("Atlas.ReeF4.chart9ToOpposite_equivariant", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "theorem"), ("Atlas.ReeF4.chart9ToOpposite_injective", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.chart9ToOpposite_surjective", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.chart9_transport_exists", "Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity", "theorem"), ("Atlas.ReeF4.chartFinalWeyl_root", "Atlas.LinearGroups.ReeF4.ChartTerminalEndpoints", "theorem"), ("Atlas.ReeF4.chartLongConjugate", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "definition"), ("Atlas.ReeF4.chartLongConjugate_eq_positive_0", "Atlas.LinearGroups.ReeF4.ChartLongConjugate0", "theorem"), ("Atlas.ReeF4.chartLongConjugate_eq_positive_1", "Atlas.LinearGroups.ReeF4.ChartLongConjugate1", "theorem"), ("Atlas.ReeF4.chartLongConjugate_eq_positive_2", "Atlas.LinearGroups.ReeF4.ChartLongConjugate2", "theorem"), ("Atlas.ReeF4.chartLongConjugate_eq_positive_3", "Atlas.LinearGroups.ReeF4.ChartLongConjugate3", "theorem"), ("Atlas.ReeF4.chartLongConjugate_formula_0", "Atlas.LinearGroups.ReeF4.ChartLongConjugate0", "theorem"), ("Atlas.ReeF4.chartLongConjugate_formula_1", "Atlas.LinearGroups.ReeF4.ChartLongConjugate1", "theorem"), ("Atlas.ReeF4.chartLongConjugate_formula_2", "Atlas.LinearGroups.ReeF4.ChartLongConjugate2", "theorem"), ("Atlas.ReeF4.chartLongConjugate_formula_3", "Atlas.LinearGroups.ReeF4.ChartLongConjugate3", "theorem"), ("Atlas.ReeF4.chartLongConjugate_val", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "theorem"), ("Atlas.ReeF4.chartLongPermutation", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "definition"), ("Atlas.ReeF4.chartLongPrefix", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "definition"), ("Atlas.ReeF4.chartLongPrefix_compatible", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "theorem"), ("Atlas.ReeF4.chartShortConjugate", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "definition"), ("Atlas.ReeF4.chartShortConjugate_eq_positive_0", "Atlas.LinearGroups.ReeF4.ChartShortConjugate0", "theorem"), ("Atlas.ReeF4.chartShortConjugate_eq_positive_1", "Atlas.LinearGroups.ReeF4.ChartShortConjugate1", "theorem"), ("Atlas.ReeF4.chartShortConjugate_eq_positive_2", "Atlas.LinearGroups.ReeF4.ChartShortConjugate2", "theorem"), ("Atlas.ReeF4.chartShortConjugate_formula_0", "Atlas.LinearGroups.ReeF4.ChartShortConjugate0", "theorem"), ("Atlas.ReeF4.chartShortConjugate_formula_1", "Atlas.LinearGroups.ReeF4.ChartShortConjugate1", "theorem"), ("Atlas.ReeF4.chartShortConjugate_formula_2", "Atlas.LinearGroups.ReeF4.ChartShortConjugate2", "theorem"), ("Atlas.ReeF4.chartShortConjugate_val", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "theorem"), ("Atlas.ReeF4.chartShortPermutation", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "definition"), ("Atlas.ReeF4.chartShortPrefix", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "definition"), ("Atlas.ReeF4.chartShortPrefix_compatible", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "theorem"), ("Atlas.ReeF4.chartTerminalWord_inverse_root", "Atlas.LinearGroups.ReeF4.ChartTerminalEndpoints", "theorem"), ("Atlas.ReeF4.chartTransportProduct", "Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity", "definition"), ("Atlas.ReeF4.chartTransportProduct_factorization", "Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity", "theorem"), ("Atlas.ReeF4.chartUnipotentWord", "Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity", "definition"), ("Atlas.ReeF4.chartUnipotentWord_mem", "Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity", "theorem"), ("Atlas.ReeF4.elementary_oppositePair_to_base", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "theorem"), ("Atlas.ReeF4.elementary_specialOppositePair_transitive", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "theorem"), ("Atlas.ReeF4.firstRoot_polar_coordinate", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.first_opposite_specialOpposite", "Atlas.LinearGroups.ReeF4.SpecialOppositePairs", "theorem"), ("Atlas.ReeF4.fullOppositePairStabilizer", "Atlas.LinearGroups.ReeF4.SpecialOppositePairCount", "definition"), ("Atlas.ReeF4.modelConjugate_formula", "Atlas.LinearGroups.ReeF4.ChartPositiveConjugates", "theorem"), ("Atlas.ReeF4.model_oppositePair_to_base", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "theorem"), ("Atlas.ReeF4.model_order_of_fullPairStabilizer_order", "Atlas.LinearGroups.ReeF4.SpecialOppositePairCount", "theorem"), ("Atlas.ReeF4.model_order_oppositePair_factorization", "Atlas.LinearGroups.ReeF4.SpecialOppositePairCount", "theorem"), ("Atlas.ReeF4.model_preserves_polar", "Atlas.LinearGroups.ReeF4.SpecialOppositeAction", "theorem"), ("Atlas.ReeF4.model_specialOppositePairs_pretransitive", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "theorem"), ("Atlas.ReeF4.oppositeFiberEquiv", "Atlas.LinearGroups.ReeF4.SpecialOppositePairCount", "definition"), ("Atlas.ReeF4.oppositeSpecialPointsEquivChart9", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "definition"), ("Atlas.ReeF4.polar_nonzero_mk_reps_iff", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.polar_nonzero_units_smul_iff", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.positiveRootNormalizedHighestAction", "Atlas.LinearGroups.ReeF4.PositiveRootPointAction", "definition"), ("Atlas.ReeF4.positiveRootNormalizedHighestAction_val", "Atlas.LinearGroups.ReeF4.PositiveRootPointAction", "theorem"), ("Atlas.ReeF4.positiveRootOppositeAction", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "definition"), ("Atlas.ReeF4.positiveRootOppositeAction_val", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "theorem"), ("Atlas.ReeF4.positiveRootSubgroup_fixes_firstSpecialPoint", "Atlas.LinearGroups.ReeF4.PositiveRootPointAction", "theorem"), ("Atlas.ReeF4.positiveRootSubgroup_fixes_lowestRoot", "Atlas.LinearGroups.ReeF4.PositiveRootPointAction", "theorem"), ("Atlas.ReeF4.positiveRootSubgroup_preserves_highestCoefficient", "Atlas.LinearGroups.ReeF4.PositiveRootPointAction", "theorem"), ("Atlas.ReeF4.positiveRoot_chart9_orbit", "Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity", "theorem"), ("Atlas.ReeF4.positiveRoot_chart9_transitive", "Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity", "theorem"), ("Atlas.ReeF4.positiveRoot_oppositePoint_pretransitive", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "theorem"), ("Atlas.ReeF4.positiveRoot_oppositePoint_transitive", "Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity", "theorem"), ("Atlas.ReeF4.specialOppositePairsAction", "Atlas.LinearGroups.ReeF4.SpecialOppositePairs", "definition"), ("Atlas.ReeF4.specialOppositePairsEquivSigma", "Atlas.LinearGroups.ReeF4.SpecialOppositePairCount", "definition"), ("Atlas.ReeF4.specialOpposite_first_iff", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.specialOpposite_irrefl", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.specialOpposite_mk_iff", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem"), ("Atlas.ReeF4.specialOpposite_model_iff", "Atlas.LinearGroups.ReeF4.SpecialOppositeAction", "theorem"), ("Atlas.ReeF4.specialOpposite_symm", "Atlas.LinearGroups.ReeF4.SpecialOppositePoints", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "/home/gerald/atlas/claude/release-update-v1.2-20261030/verification-runs/20261030T093029-audit-batch-batch-008-large-ree"
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
