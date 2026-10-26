import Atlas.Tits.Order
import Atlas.Tits.Simplicity
import Atlas.Tits.RetainedAction
import Atlas.Tits.Construction
import Atlas.Tits.CharacterConsequences
import Atlas.Tits.PointRowKernelOrder
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Tits.Ambient", "Atlas.Tits.LocalGroups", "definition"), ("Atlas.Tits.Model", "Atlas.Tits.LocalGroups", "definition"), ("Atlas.Tits.Neighbours", "Atlas.Tits.LocalGroups", "definition"), ("Atlas.Tits.alpha_not_mem_derived", "Atlas.Tits.CharacterConsequences", "theorem"), ("Atlas.Tits.alpha_square_mem_derived", "Atlas.Tits.CharacterConsequences", "theorem"), ("Atlas.Tits.ambientStabilizer", "Atlas.Tits.LocalGroups", "definition"), ("Atlas.Tits.ambient_generated_by_derived_alpha", "Atlas.Tits.CharacterConsequences", "theorem"), ("Atlas.Tits.card", "Atlas.Tits.Order", "theorem"), ("Atlas.Tits.cardAmbient", "Atlas.Tits.LocalGroups", "theorem"), ("Atlas.Tits.cardNeighbours", "Atlas.Tits.LocalGroups", "theorem"), ("Atlas.Tits.construction", "Atlas.Tits.Construction", "theorem"), ("Atlas.Tits.derivedSubgroup", "Atlas.Tits.LocalGroups", "definition"), ("Atlas.Tits.derived_eq_transferKernel", "Atlas.Tits.Order", "theorem"), ("Atlas.Tits.derived_ne_bot", "Atlas.Tits.Order", "theorem"), ("Atlas.Tits.embeddingIntoRudvalis", "Atlas.Tits.LocalGroups", "definition"), ("Atlas.Tits.embeddingIntoRudvalis_injective", "Atlas.Tits.LocalGroups", "theorem"), ("Atlas.Tits.embedding_range_card", "Atlas.Tits.RetainedAction", "theorem"), ("Atlas.Tits.embedding_range_index", "Atlas.Tits.RetainedAction", "theorem"), ("Atlas.Tits.finite", "Atlas.Tits.Construction", "theorem"), ("Atlas.Tits.index_derived", "Atlas.Tits.Order", "theorem"), ("Atlas.Tits.isSimpleGroup", "Atlas.Tits.Simplicity", "theorem"), ("Atlas.Tits.localProjection_surjective", "Atlas.Tits.LocalGroups", "theorem"), ("Atlas.Tits.mem_transfer_range_iff", "Atlas.Tits.CharacterConsequences", "theorem"), ("Atlas.Tits.modelEquivTransferKernel", "Atlas.Tits.CharacterConsequences", "definition"), ("Atlas.Tits.model_is_derived", "Atlas.Tits.Construction", "theorem"), ("Atlas.Tits.model_neighbour_stabilizer_card", "Atlas.Tits.RetainedAction", "theorem"), ("Atlas.Tits.model_neighbours_faithful", "Atlas.Tits.RetainedAction", "theorem"), ("Atlas.Tits.model_neighbours_transitive", "Atlas.Tits.RetainedAction", "any"), ("Atlas.Tits.monomialPointRowKernel", "Atlas.Tits.PointRowKernelOrder", "definition"), ("Atlas.Tits.monomialPointRowKernel_card", "Atlas.Tits.PointRowKernelOrder", "theorem"), ("Atlas.Tits.monomialPointRowKernel_index", "Atlas.Tits.PointRowKernelOrder", "theorem"), ("Atlas.Tits.nonabelian", "Atlas.Tits.Simplicity", "theorem"), ("Atlas.Tits.noncommutative", "Atlas.Tits.Simplicity", "theorem"), ("Atlas.Tits.normal_subgroups", "Atlas.Tits.Order", "theorem"), ("Atlas.Tits.order", "Atlas.Tits.Construction", "theorem"), ("Atlas.Tits.perfect", "Atlas.Tits.Simplicity", "theorem"), ("Atlas.Tits.point_scalar_kernel_le_row_kernel", "Atlas.Tits.PointRowKernelOrder", "theorem"), ("Atlas.Tits.transfer", "Atlas.Tits.TransferDefinition", "definition"), ("Atlas.Tits.transfer_alpha", "Atlas.Tits.TransferEvaluation", "theorem"), ("Atlas.Tits.transfer_nontrivial", "Atlas.Tits.Order", "theorem"), ("Atlas.Tits.transfer_range_order", "Atlas.Tits.Order", "theorem"), ("Atlas.Tits.transfer_range_set", "Atlas.Tits.CharacterConsequences", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/tits-public/20260925T041620-3"
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
