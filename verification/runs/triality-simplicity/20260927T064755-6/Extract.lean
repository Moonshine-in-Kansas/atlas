import Atlas.LinearGroups.Triality.Simplicity
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Triality.ParabolicPoints", "Atlas.LinearGroups.Triality.ParabolicAction", "any"), ("Atlas.Triality.borel_opposite_intersection_le_torus", "Atlas.LinearGroups.Triality.ParabolicCoreReduction", "any"), ("Atlas.Triality.firstLine_coordinate_zero", "Atlas.LinearGroups.Triality.ParabolicCoreReduction", "any"), ("Atlas.Triality.longRootCell_entry", "Atlas.LinearGroups.Triality.ParabolicCoreReduction", "any"), ("Atlas.Triality.noncommutative", "Atlas.LinearGroups.Triality.Perfect", "any"), ("Atlas.Triality.normal_in_longParabolic_eq_bot", "Atlas.LinearGroups.Triality.TorusCore", "any"), ("Atlas.Triality.normal_in_longParabolic_le_borel", "Atlas.LinearGroups.Triality.ParabolicCoreReduction", "any"), ("Atlas.Triality.normal_in_longParabolic_le_torus", "Atlas.LinearGroups.Triality.ParabolicCoreReduction", "any"), ("Atlas.Triality.normal_in_torus_eq_bot", "Atlas.LinearGroups.Triality.TorusCore", "any"), ("Atlas.Triality.parabolic", "Atlas.LinearGroups.Triality.ParabolicAction", "any"), ("Atlas.Triality.parabolicPoints_faithful", "Atlas.LinearGroups.Triality.ParabolicAction", "any"), ("Atlas.Triality.parabolicPoints_nontrivial", "Atlas.LinearGroups.Triality.ParabolicAction", "any"), ("Atlas.Triality.parabolicPoints_primitive", "Atlas.LinearGroups.Triality.ParabolicAction", "any"), ("Atlas.Triality.parabolicRadical", "Atlas.LinearGroups.Triality.Simplicity", "any"), ("Atlas.Triality.parabolicRadical_le", "Atlas.LinearGroups.Triality.Simplicity", "any"), ("Atlas.Triality.parabolicRadical_normal", "Atlas.LinearGroups.Triality.Simplicity", "any"), ("Atlas.Triality.parabolicRadical_solvable", "Atlas.LinearGroups.Triality.Simplicity", "any"), ("Atlas.Triality.parabolic_isCoatom", "Atlas.LinearGroups.Triality.ParabolicAction", "any"), ("Atlas.Triality.parabolic_ne_top", "Atlas.LinearGroups.Triality.ParabolicAction", "any"), ("Atlas.Triality.parabolic_normalCore_eq_bot", "Atlas.LinearGroups.Triality.ParabolicAction", "any"), ("Atlas.Triality.shortWeyl_inv_e_zero", "Atlas.LinearGroups.Triality.ParabolicCoreReduction", "any"), ("Atlas.Triality.simple", "Atlas.LinearGroups.Triality.Simplicity", "any"), ("Atlas.Triality.torusScale_fixed_all", "Atlas.LinearGroups.Triality.TorusCore", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/triality-simplicity/20260927T064755-6"
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
