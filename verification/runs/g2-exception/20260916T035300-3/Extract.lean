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
  let rootSpecs : Array (String × String × String) := #[("Atlas.G2.Binary.IsLine", "Atlas.LinearGroups.G2.BinaryHexagon", "any"), ("Atlas.G2.Binary.Line", "Atlas.LinearGroups.G2.BinaryHexagon", "any"), ("Atlas.G2.Binary.Singular", "Atlas.LinearGroups.G2.BinaryHexagon", "any"), ("Atlas.G2.Binary.card_Line", "Atlas.LinearGroups.G2.BinaryHexagon", "any"), ("Atlas.G2.Binary.card_fixed_rootA", "Atlas.LinearGroups.G2.BinaryHexagon", "any"), ("Atlas.G2.Binary.card_fixed_rootF", "Atlas.LinearGroups.G2.BinaryHexagon", "any"), ("Atlas.G2.Binary.lineAction", "Atlas.LinearGroups.G2.BinaryHexagon", "any"), ("Atlas.G2.Binary.lineSign", "Atlas.LinearGroups.G2.BinaryHexagon", "any"), ("Atlas.G2.Binary.lineSign_rootA", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.Binary.lineSign_rootF_one", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.Binary.lineSign_surjective", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.BinaryException.H", "Atlas.LinearGroups.G2.BinaryIndex", "any"), ("Atlas.G2.BinaryException.H_ne_bot", "Atlas.LinearGroups.G2.BinaryIndex", "any"), ("Atlas.G2.BinaryException.H_proper", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.BinaryException.H_singularPoints_pretransitive", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.BinaryException.card_H", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.BinaryException.card_H_pointStabilizer", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.BinaryException.index_H", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.BinaryException.index_le_two", "Atlas.LinearGroups.G2.BinaryIndex", "any"), ("Atlas.G2.BinaryException.lineSign_kernel", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.BinaryException.not_simple", "Atlas.LinearGroups.G2.BinarySign", "any"), ("Atlas.G2.ExceptionChecks.binary_exact_range", "Atlas.LinearGroups.G2.ExceptionChecks", "any"), ("Atlas.G2.ExceptionChecks.binary_index", "Atlas.LinearGroups.G2.ExceptionChecks", "any"), ("Atlas.G2.ExceptionChecks.binary_normal_order", "Atlas.LinearGroups.G2.ExceptionChecks", "any"), ("Atlas.G2.ExceptionChecks.binary_not_simple", "Atlas.LinearGroups.G2.ExceptionChecks", "any"), ("Atlas.G2.ExceptionChecks.four_exact_range", "Atlas.LinearGroups.G2.ExceptionChecks", "any"), ("Atlas.G2.ExceptionChecks.ternary_exact_range", "Atlas.LinearGroups.G2.ExceptionChecks", "any"), ("Atlas.G2.card_longRootNormalClosure_binary", "Atlas.LinearGroups.G2.BinaryException", "any"), ("Atlas.G2.fieldEquiv_longRootNormalClosure_map", "Atlas.LinearGroups.G2.LocalFieldTransport", "any"), ("Atlas.G2.index_longRootNormalClosure_binary", "Atlas.LinearGroups.G2.BinaryException", "any"), ("Atlas.G2.isSimple_iff", "Atlas.LinearGroups.G2.BinaryException", "any"), ("Atlas.G2.longRootNormalClosureFieldEquiv", "Atlas.LinearGroups.G2.LocalFieldTransport", "any"), ("Atlas.G2.longRootNormalClosure_binary_nontrivial", "Atlas.LinearGroups.G2.BinaryException", "any"), ("Atlas.G2.longRootNormalClosure_binary_proper", "Atlas.LinearGroups.G2.BinaryException", "any"), ("Atlas.G2.not_simple_binary", "Atlas.LinearGroups.G2.BinaryException", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/g2-exception/20260916T035300-3"
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
