import Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeCoordinates
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeIsometry
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeSpanning
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Orthogonal.Minus.compound_dagger", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.compound_mul", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.compound_one", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.exteriorMap_scalar_of_hodgeFixed", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeSpanning", "any"), ("Atlas.Orthogonal.Minus.exterior_commutes_hodge", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.exterior_preserves_hermitian", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.exterior_preserves_pfaffian_polar", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.firstThree", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.fixedVector", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.fixedVector_fixed", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.fixedVector_pfaffian", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hermitian_hodge_polar", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.hodge", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodgeCoordinates", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodgeCoordinatesIsometry", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodgeFixed", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodgeFixedAction", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.hodgeFixedAction_preserves", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.hodgeFixedForm", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodgeFixedForm_pfaffian", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodgeFixedHom", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.hodgeFixed_finrank", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodgeFixed_linear_ext", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeSpanning", "any"), ("Atlas.Orthogonal.Minus.hodgeLinear", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodge_add", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodge_base_smul", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodge_involutive", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodge_smul", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.hodge_symmetrize_mem", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeSpanning", "any"), ("Atlas.Orthogonal.Minus.matrix_scalar_of_hodgeFixed_scalar", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeSpanning", "any"), ("Atlas.Orthogonal.Minus.normTripleForm", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge", "any"), ("Atlas.Orthogonal.Minus.rankThreeHodgeIsometry", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeIsometry", "any"), ("Atlas.Orthogonal.Minus.rankThreeNormCoordinates", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeCoordinates", "any"), ("Atlas.Orthogonal.Minus.rankThreeNormCoordinates_form", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeCoordinates", "any"), ("Atlas.Orthogonal.Minus.rankThreeNormIsometry", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeIsometry", "any"), ("Atlas.Orthogonal.Minus.rankThreePlaneCoordinates", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeCoordinates", "any"), ("Atlas.Orthogonal.Minus.rankThreePlaneCoordinates_form", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeCoordinates", "any"), ("Atlas.Orthogonal.Minus.suExteriorEquiv", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.suExteriorUnitary", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction", "any"), ("Atlas.Orthogonal.Minus.tracePairCoordinates", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeCoordinates", "any"), ("Atlas.Orthogonal.Minus.tracePairCoordinates_form", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeCoordinates", "any"), ("Atlas.Orthogonal.Minus.tripleCoordinates", "Atlas.LinearGroups.Orthogonal.Minus.RankThreeIsometry", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/minus-orthogonal-rank-three-structure/20260927T013717-5"
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
