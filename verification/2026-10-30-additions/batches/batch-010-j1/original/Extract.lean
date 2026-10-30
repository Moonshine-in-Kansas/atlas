import Atlas.Sporadic.Janko1.Local168
import Atlas.Sporadic.Janko1.SignConjugation
import Atlas.Sporadic.Janko1.SignGroup
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Janko1.H_eq_signSubgroup_sup_pqSubgroup", "Atlas.Sporadic.Janko1.Local168", "theorem"), ("Atlas.Janko1.H_normal_form", "Atlas.Sporadic.Janko1.Local168", "theorem"), ("Atlas.Janko1.P_conjugates_sign", "Atlas.Sporadic.Janko1.SignConjugation", "theorem"), ("Atlas.Janko1.P_signElement", "Atlas.Sporadic.Janko1.SignConjugation", "theorem"), ("Atlas.Janko1.Q_conjugates_sign", "Atlas.Sporadic.Janko1.SignConjugation", "theorem"), ("Atlas.Janko1.Q_signElement", "Atlas.Sporadic.Janko1.SignConjugation", "theorem"), ("Atlas.Janko1.card_H", "Atlas.Sporadic.Janko1.Local168", "theorem"), ("Atlas.Janko1.card_signSubgroup", "Atlas.Sporadic.Janko1.SignGroup", "theorem"), ("Atlas.Janko1.coordinateRepresentation_signElement", "Atlas.Sporadic.Janko1.SignConjugation", "theorem"), ("Atlas.Janko1.hMultiply", "Atlas.Sporadic.Janko1.Local168", "definition"), ("Atlas.Janko1.hMultiply_bijective", "Atlas.Sporadic.Janko1.Local168", "theorem"), ("Atlas.Janko1.hNormalFormEquiv", "Atlas.Sporadic.Janko1.Local168", "definition"), ("Atlas.Janko1.hNormalFormEquiv_apply", "Atlas.Sporadic.Janko1.Local168", "theorem"), ("Atlas.Janko1.hProductEquiv", "Atlas.Sporadic.Janko1.Local168", "definition"), ("Atlas.Janko1.pqSubgroup_le_sign_normalizer", "Atlas.Sporadic.Janko1.Local168", "theorem"), ("Atlas.Janko1.signDouble", "Atlas.Sporadic.Janko1.SignConjugation", "definition"), ("Atlas.Janko1.signElement", "Atlas.Sporadic.Janko1.SignGroup", "definition"), ("Atlas.Janko1.signElement_basis_zero", "Atlas.Sporadic.Janko1.SignConjugation", "theorem"), ("Atlas.Janko1.signEquiv", "Atlas.Sporadic.Janko1.SignGroup", "definition"), ("Atlas.Janko1.signHom", "Atlas.Sporadic.Janko1.SignGroup", "definition"), ("Atlas.Janko1.signHom_injective", "Atlas.Sporadic.Janko1.SignGroup", "theorem"), ("Atlas.Janko1.signLinear_mul", "Atlas.Sporadic.Janko1.SignGroup", "theorem"), ("Atlas.Janko1.signShift", "Atlas.Sporadic.Janko1.SignConjugation", "definition"), ("Atlas.Janko1.signSubgroup", "Atlas.Sporadic.Janko1.SignGroup", "definition"), ("Atlas.Janko1.signSubgroupEquiv", "Atlas.Sporadic.Janko1.SignGroup", "definition"), ("Atlas.Janko1.signSubgroup_comm", "Atlas.Sporadic.Janko1.SignGroup", "theorem"), ("Atlas.Janko1.signSubgroup_square", "Atlas.Sporadic.Janko1.SignGroup", "theorem"), ("Atlas.Janko1.sign_pq_disjoint", "Atlas.Sporadic.Janko1.Local168", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "/home/gerald/atlas/claude/release-update-v1.2-20261030/verification-runs/20261030T093839-audit-batch-batch-010-j1"
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
