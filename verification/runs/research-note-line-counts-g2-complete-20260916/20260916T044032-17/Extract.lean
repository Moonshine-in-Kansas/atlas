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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Families.Alternating.card_factorial", "", "theorem"), ("Atlas.Families.Alternating.isSimpleGroup", "", "theorem"), ("Atlas.Families.Cyclic.card", "", "theorem"), ("Atlas.Families.Cyclic.isSimpleGroup", "", "theorem"), ("Atlas.G2.card_Model", "Atlas.LinearGroups.G2.Order", "theorem"), ("Atlas.G2.isSimple_iff", "Atlas.LinearGroups.G2.BinaryException", "theorem"), ("Atlas.Orthogonal.B_card_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanks", "theorem"), ("Atlas.Orthogonal.B_simple_iff_all_rank", "Atlas.LinearGroups.Orthogonal.BAllRanksConstruction", "theorem"), ("Atlas.Orthogonal.DPlus_card", "Atlas.LinearGroups.Orthogonal.DFamily", "theorem"), ("Atlas.Orthogonal.DPlus_simple", "Atlas.LinearGroups.Orthogonal.DConstruction", "theorem"), ("Atlas.Sporadic.Conway1.card", "", "theorem"), ("Atlas.Sporadic.Conway1.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Conway2.card", "", "theorem"), ("Atlas.Sporadic.Conway2.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Conway3.card", "", "theorem"), ("Atlas.Sporadic.Conway3.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Fischer22.card", "", "theorem"), ("Atlas.Sporadic.Fischer22.simple", "", "theorem"), ("Atlas.Sporadic.Fischer23.card", "", "theorem"), ("Atlas.Sporadic.Fischer23.simple", "", "theorem"), ("Atlas.Sporadic.Fischer24Prime.card", "", "theorem"), ("Atlas.Sporadic.Fischer24Prime.simple", "", "theorem"), ("Atlas.Sporadic.HigmanSims.card", "", "theorem"), ("Atlas.Sporadic.HigmanSims.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Janko2.card", "", "theorem"), ("Atlas.Sporadic.Janko2.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Mathieu11.card", "", "theorem"), ("Atlas.Sporadic.Mathieu11.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Mathieu12.card", "", "theorem"), ("Atlas.Sporadic.Mathieu12.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Mathieu22.card", "", "theorem"), ("Atlas.Sporadic.Mathieu22.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Mathieu23.card", "", "theorem"), ("Atlas.Sporadic.Mathieu23.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Mathieu24.card", "", "theorem"), ("Atlas.Sporadic.Mathieu24.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.McLaughlin.card", "", "theorem"), ("Atlas.Sporadic.McLaughlin.isSimpleGroup", "", "theorem"), ("Atlas.Sporadic.Suzuki.card", "", "theorem"), ("Atlas.Sporadic.Suzuki.isSimpleGroup", "", "theorem"), ("Atlas.Symplectic.card_psp", "Atlas.LinearGroups.Symplectic.ProjectiveOrder", "theorem"), ("Atlas.Symplectic.simple_iff_good", "Atlas.LinearGroups.Symplectic.Exceptions", "theorem"), ("Atlas.card_psl_factor", "", "theorem"), ("Atlas.psl_simple_iff", "", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/research-note-line-counts-g2-complete-20260916/20260916T044032-17"
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
