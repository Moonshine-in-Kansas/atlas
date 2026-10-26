import Atlas.LinearGroups.Triality.Order
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.GroupTheory.card_doubleCoset_mul_intersection", "Atlas.GroupTheory.DoubleCosetCard", "any"), ("Atlas.GroupTheory.doubleCosetFiberMap", "Atlas.GroupTheory.DoubleCosetCard", "any"), ("Atlas.GroupTheory.doubleCosetFiberMap_bijective", "Atlas.GroupTheory.DoubleCosetCard", "any"), ("Atlas.GroupTheory.doubleCosetIntersection", "Atlas.GroupTheory.DoubleCosetCard", "any"), ("Atlas.GroupTheory.doubleCosetMap", "Atlas.GroupTheory.DoubleCosetCard", "any"), ("Atlas.GroupTheory.doubleCosetMap_surjective", "Atlas.GroupTheory.DoubleCosetCard", "any"), ("Atlas.Triality.AllowedCoordinate", "Atlas.LinearGroups.Triality.SurvivingParameterCard", "any"), ("Atlas.Triality.BruhatCell", "Atlas.LinearGroups.Triality.BruhatCard", "any"), ("Atlas.Triality.SurvivingParameters", "Atlas.LinearGroups.Triality.BruhatIntersection", "any"), ("Atlas.Triality.allowedCoordinateFalse", "Atlas.LinearGroups.Triality.SurvivingParameterCard", "any"), ("Atlas.Triality.allowedCoordinateTrue", "Atlas.LinearGroups.Triality.SurvivingParameterCard", "any"), ("Atlas.Triality.borelIntersection", "Atlas.LinearGroups.Triality.BruhatIntersectionCoordinates", "any"), ("Atlas.Triality.borelIntersectionCoordinates", "Atlas.LinearGroups.Triality.BruhatIntersectionCoordinates", "any"), ("Atlas.Triality.borelIntersectionMap", "Atlas.LinearGroups.Triality.BruhatIntersectionCoordinates", "any"), ("Atlas.Triality.borelIntersectionMap_bijective", "Atlas.LinearGroups.Triality.BruhatIntersectionCoordinates", "any"), ("Atlas.Triality.borelWord_conjugate_iff", "Atlas.LinearGroups.Triality.BruhatIntersectionExact", "any"), ("Atlas.Triality.borel_below", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.borel_diagonal_ne_zero", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.borel_weyl_eq_weyl_borel", "Atlas.LinearGroups.Triality.BruhatDisjoint", "any"), ("Atlas.Triality.bruhatCellsEquiv", "Atlas.LinearGroups.Triality.BruhatCard", "any"), ("Atlas.Triality.bruhatCellsMap", "Atlas.LinearGroups.Triality.BruhatCard", "any"), ("Atlas.Triality.bruhatCellsMap_bijective", "Atlas.LinearGroups.Triality.BruhatCard", "any"), ("Atlas.Triality.bruhat_cells_disjoint", "Atlas.LinearGroups.Triality.BruhatDisjoint", "any"), ("Atlas.Triality.bruhat_unique_index", "Atlas.LinearGroups.Triality.BruhatDisjoint", "any"), ("Atlas.Triality.card_allowedCoordinate", "Atlas.LinearGroups.Triality.SurvivingParameterCard", "any"), ("Atlas.Triality.card_borelIntersection", "Atlas.LinearGroups.Triality.SurvivingParameterCard", "any"), ("Atlas.Triality.card_bruhatCell", "Atlas.LinearGroups.Triality.BruhatCard", "any"), ("Atlas.Triality.card_group", "Atlas.LinearGroups.Triality.Order", "any"), ("Atlas.Triality.card_group_bruhat_sum", "Atlas.LinearGroups.Triality.BruhatCard", "any"), ("Atlas.Triality.card_survivingParameters", "Atlas.LinearGroups.Triality.SurvivingParameterCard", "any"), ("Atlas.Triality.coordinateHeight", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.coordinateWord_height_separates", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.coordinateWord_injective", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.longSigned_conjugate_mem", "Atlas.LinearGroups.Triality.BruhatIntersectionExact", "any"), ("Atlas.Triality.mem_borelIntersection", "Atlas.LinearGroups.Triality.BruhatIntersectionCoordinates", "any"), ("Atlas.Triality.positiveMatrix_below", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.positiveMatrix_diagonal", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.positive_conjugate_iff", "Atlas.LinearGroups.Triality.BruhatIntersectionExact", "any"), ("Atlas.Triality.positive_conjugate_of_surviving", "Atlas.LinearGroups.Triality.BruhatIntersectionExact", "any"), ("Atlas.Triality.rootEntry", "Atlas.LinearGroups.Triality.BruhatIntersection", "any"), ("Atlas.Triality.rootSurvives", "Atlas.LinearGroups.Triality.BruhatIntersection", "any"), ("Atlas.Triality.rootSurvives_entry", "Atlas.LinearGroups.Triality.BruhatIntersection", "any"), ("Atlas.Triality.rootSurvives_table", "Atlas.LinearGroups.Triality.SurvivingParameterCard", "any"), ("Atlas.Triality.rootSurvives_u", "Atlas.LinearGroups.Triality.BruhatIntersection", "any"), ("Atlas.Triality.rootSurvives_v", "Atlas.LinearGroups.Triality.BruhatIntersection", "any"), ("Atlas.Triality.shortSigned_conjugate_mem", "Atlas.LinearGroups.Triality.BruhatIntersectionExact", "any"), ("Atlas.Triality.survivingCoordinates", "Atlas.LinearGroups.Triality.SurvivingParameterCard", "any"), ("Atlas.Triality.survivingParameters_of_conjugate", "Atlas.LinearGroups.Triality.BruhatIntersection", "any"), ("Atlas.Triality.torus_single", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.weightedLength_le", "Atlas.LinearGroups.Triality.BruhatCard", "any"), ("Atlas.Triality.weylLift_single", "Atlas.LinearGroups.Triality.BorelTriangular", "any"), ("Atlas.Triality.weyl_conjugate_below", "Atlas.LinearGroups.Triality.BruhatIntersection", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/triality-order/20260927T063706-6"
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
