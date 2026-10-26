import Atlas.LinearGroups.Orthogonal.Minus.Family
import Atlas.LinearGroups.Type2D
import Atlas.LinearGroups.Orthogonal.Minus.FieldTransport
import Atlas.LinearGroups.Orthogonal.Minus.KernelTransport
import Atlas.LinearGroups.Orthogonal.Minus.WittIndex
import Atlas.LinearGroups.Orthogonal.Minus.FullOrder
import Atlas.LinearGroups.Orthogonal.Minus.CenterOdd
import Atlas.LinearGroups.Orthogonal.Minus.IntrinsicOdd
import Atlas.LinearGroups.Orthogonal.Minus.IntrinsicEven
import Atlas.LinearGroups.Orthogonal.Minus.OrderChecks
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Orthogonal.DMinus", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.DMinus", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.card_elementary_center_mul_two", "Atlas.LinearGroups.Orthogonal.Minus.CenterOdd", "any"), ("Atlas.Orthogonal.Minus.card_full", "Atlas.LinearGroups.Orthogonal.Minus.FullOrder", "any"), ("Atlas.Orthogonal.Minus.elementary_eq_intrinsic_kernel", "Atlas.LinearGroups.Orthogonal.Minus.IntrinsicOdd", "any"), ("Atlas.Orthogonal.Minus.elementary_index_even", "Atlas.LinearGroups.Orthogonal.Minus.IntrinsicEven", "any"), ("Atlas.Orthogonal.Minus.elementary_index_odd", "Atlas.LinearGroups.Orthogonal.Minus.IntrinsicOdd", "any"), ("Atlas.Orthogonal.Minus.family_center_scalar", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_elementary_perfect", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_faithful", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_finite", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_full_order", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_intrinsic_even", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_intrinsic_odd", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_noncommutative", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_order", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_primitive", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_projection_kernel", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.family_simple", "Atlas.LinearGroups.Orthogonal.Minus.Family", "any"), ("Atlas.Orthogonal.Minus.fieldCoordinates_siegel", "Atlas.LinearGroups.Orthogonal.Minus.KernelTransport", "any"), ("Atlas.Orthogonal.Minus.fieldEquivProjective_projection", "Atlas.LinearGroups.Orthogonal.Minus.FieldTransport", "any"), ("Atlas.Orthogonal.Minus.fullDickson_field_transport", "Atlas.LinearGroups.Orthogonal.Minus.KernelTransport", "any"), ("Atlas.Orthogonal.Minus.fullDickson_kernel_elementary", "Atlas.LinearGroups.Orthogonal.Minus.IntrinsicEven", "any"), ("Atlas.Orthogonal.Minus.order_rank_four_binary", "Atlas.LinearGroups.Orthogonal.Minus.OrderChecks", "any"), ("Atlas.Orthogonal.Minus.order_rank_four_ternary", "Atlas.LinearGroups.Orthogonal.Minus.OrderChecks", "any"), ("Atlas.Orthogonal.Minus.order_rank_three_binary", "Atlas.LinearGroups.Orthogonal.Minus.OrderChecks", "any"), ("Atlas.Orthogonal.Minus.order_rank_three_ternary", "Atlas.LinearGroups.Orthogonal.Minus.OrderChecks", "any"), ("Atlas.Orthogonal.Minus.witt_index_exact", "Atlas.LinearGroups.Orthogonal.Minus.WittIndex", "any"), ("Atlas.Type2DConstruction", "Atlas.LinearGroups.Type2D", "any"), ("Atlas.exists_type2D", "Atlas.LinearGroups.Type2D", "any"), ("Atlas.type2D_construction", "Atlas.LinearGroups.Type2D", "any"), ("Atlas.type2D_prime_power", "Atlas.LinearGroups.Type2D", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/minus-orthogonal-public/20260927T003817-692"
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
