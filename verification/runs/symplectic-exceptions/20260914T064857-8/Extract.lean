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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Symplectic.BinaryException.K", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "any"), ("Atlas.Symplectic.BinaryException.OddParameter", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "any"), ("Atlas.Symplectic.BinaryException.OddRefinement", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "any"), ("Atlas.Symplectic.BinaryException.Refinement", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "any"), ("Atlas.Symplectic.BinaryException.V", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "any"), ("Atlas.Symplectic.BinaryException.baseQuadratic", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "any"), ("Atlas.Symplectic.BinaryException.baseQuadratic_polar", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.binary_center_eq_bot", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.card_oddRefinement", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.card_signKernel", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.card_six_permutations", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.card_sp_binary_four", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.coordinates", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.literal", "Atlas.LinearGroups.Symplectic.BinarySixAction", "any"), ("Atlas.Symplectic.BinaryException.oddRefinementAction", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "any"), ("Atlas.Symplectic.BinaryException.oddRefinementAction_apply", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.oddRefinementEquiv", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "any"), ("Atlas.Symplectic.BinaryException.oddRefinement_faithful", "Atlas.LinearGroups.Symplectic.BinarySixAction", "any"), ("Atlas.Symplectic.BinaryException.oddSign", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "any"), ("Atlas.Symplectic.BinaryException.oddSign_surjective", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.parameterOf", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "any"), ("Atlas.Symplectic.BinaryException.parameter_refinement", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.permutationEquiv", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "any"), ("Atlas.Symplectic.BinaryException.permutationHom", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "any"), ("Atlas.Symplectic.BinaryException.permutationHom_injective", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.projectionEquiv", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "any"), ("Atlas.Symplectic.BinaryException.psp_binary_four_not_simple", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.refinementAction_apply", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.refinementEquiv", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "any"), ("Atlas.Symplectic.BinaryException.refinementOf", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "any"), ("Atlas.Symplectic.BinaryException.refinement_reconstruction", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.refinement_smul", "Atlas.LinearGroups.Symplectic.BinaryRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.signKernel", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "any"), ("Atlas.Symplectic.BinaryException.signKernel_ne_bot", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.signKernel_ne_top", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.signKernel_normal", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "any"), ("Atlas.Symplectic.BinaryException.sixForms", "Atlas.LinearGroups.Symplectic.BinarySixAction", "any"), ("Atlas.Symplectic.BinaryException.sixFormsEquiv", "Atlas.LinearGroups.Symplectic.BinarySixAction", "any"), ("Atlas.Symplectic.BinaryException.sixForms_injective", "Atlas.LinearGroups.Symplectic.BinarySixAction", "theorem"), ("Atlas.Symplectic.BinaryException.sixParameter", "Atlas.LinearGroups.Symplectic.BinarySixAction", "any"), ("Atlas.Symplectic.BinaryException.sixParameter_odd", "Atlas.LinearGroups.Symplectic.BinarySixAction", "theorem"), ("Atlas.Symplectic.BinaryException.sp_binary_four_not_simple", "Atlas.LinearGroups.Symplectic.BinarySignKernel", "theorem"), ("Atlas.Symplectic.BinaryException.zeroCount", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "any"), ("Atlas.Symplectic.BinaryException.zeroCount_invariant", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "theorem"), ("Atlas.Symplectic.BinaryException.zeroCount_refinement_iff", "Atlas.LinearGroups.Symplectic.BinaryOddRefinements", "theorem"), ("Atlas.Symplectic.FormRefinement", "Atlas.LinearGroups.Symplectic.RefinementAction", "any"), ("Atlas.Symplectic.binaryExceptionEquiv", "Atlas.LinearGroups.Symplectic.Exceptions", "any"), ("Atlas.Symplectic.binaryFieldEquiv", "Atlas.LinearGroups.Symplectic.Exceptions", "any"), ("Atlas.Symplectic.exceptionalNormal", "Atlas.LinearGroups.Symplectic.Exceptions", "any"), ("Atlas.Symplectic.exceptionalNormal_card", "Atlas.LinearGroups.Symplectic.Exceptions", "theorem"), ("Atlas.Symplectic.exceptionalNormal_ne_bot", "Atlas.LinearGroups.Symplectic.Exceptions", "theorem"), ("Atlas.Symplectic.exceptionalNormal_ne_top", "Atlas.LinearGroups.Symplectic.Exceptions", "theorem"), ("Atlas.Symplectic.exceptionalNormal_normal", "Atlas.LinearGroups.Symplectic.Exceptions", "any"), ("Atlas.Symplectic.exceptional_group_card", "Atlas.LinearGroups.Symplectic.Exceptions", "theorem"), ("Atlas.Symplectic.fieldEquivPSp", "Atlas.LinearGroups.Symplectic.FieldTransport", "any"), ("Atlas.Symplectic.fieldEquivPSp_projection", "Atlas.LinearGroups.Symplectic.FieldTransport", "theorem"), ("Atlas.Symplectic.fieldEquivSp", "Atlas.LinearGroups.Symplectic.FieldTransport", "any"), ("Atlas.Symplectic.formRefinementAction", "Atlas.LinearGroups.Symplectic.RefinementAction", "any"), ("Atlas.Symplectic.formRefinementAction_apply", "Atlas.LinearGroups.Symplectic.RefinementAction", "theorem"), ("Atlas.Symplectic.formRefinement_zeroCount_invariant", "Atlas.LinearGroups.Symplectic.RefinementAction", "theorem"), ("Atlas.Symplectic.rank_one_three_not_simple", "Atlas.LinearGroups.Symplectic.SmallRankExceptions", "theorem"), ("Atlas.Symplectic.rank_one_two_not_simple", "Atlas.LinearGroups.Symplectic.SmallRankExceptions", "theorem"), ("Atlas.Symplectic.rank_two_two_not_simple", "Atlas.LinearGroups.Symplectic.Exceptions", "theorem"), ("Atlas.Symplectic.rank_zero_not_simple", "Atlas.LinearGroups.Symplectic.SmallRankExceptions", "theorem"), ("Atlas.Symplectic.simple_iff_good", "Atlas.LinearGroups.Symplectic.Exceptions", "theorem")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/symplectic-exceptions/20260914T064857-8"
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
