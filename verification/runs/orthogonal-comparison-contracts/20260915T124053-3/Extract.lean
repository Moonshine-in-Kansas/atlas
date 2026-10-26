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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Comparisons.Classical.b1EquivA1", "Atlas.Comparisons.Classical.Orthogonal", "any"), ("Atlas.Comparisons.Classical.b2EquivC2", "Atlas.Comparisons.Classical.Orthogonal", "any"), ("Atlas.Comparisons.Classical.bFieldEquiv", "Atlas.Comparisons.Classical.Orthogonal", "any"), ("Atlas.Comparisons.Classical.d2EquivProduct", "Atlas.Comparisons.Classical.Orthogonal", "any"), ("Atlas.Comparisons.Classical.d3EquivA3", "Atlas.Comparisons.Classical.Orthogonal", "any"), ("Atlas.Comparisons.Classical.dFieldEquiv", "Atlas.Comparisons.Classical.Orthogonal", "any"), ("Atlas.Comparisons.Classical.evenBEquivC", "Atlas.Comparisons.Classical.Orthogonal", "any"), ("Atlas.Comparisons.Classical.oddB_C_involution_counts", "Atlas.Comparisons.Classical.OrthogonalInvolutions", "theorem"), ("Atlas.Comparisons.Classical.oddB_card_eq_C", "Atlas.Comparisons.Classical.OrthogonalOrder", "theorem"), ("Atlas.Comparisons.Classical.oddB_not_equiv_C", "Atlas.Comparisons.Classical.OrthogonalInvolutions", "theorem"), ("Atlas.Comparisons.Classical.oddB_same_order_nonisomorphic_C", "Atlas.Comparisons.Classical.OrthogonalInvolutions", "theorem"), ("Atlas.Comparisons.Exceptional.DeletedEight.alternatingHom_elementary", "Atlas.Comparisons.Exceptional.Order20160A8", "any"), ("Atlas.Comparisons.Exceptional.DeletedEight.permutationHom", "Atlas.Comparisons.Exceptional.DeletedEightFaithful", "any"), ("Atlas.Comparisons.Exceptional.DeletedEight.permutationHom_injective", "Atlas.Comparisons.Exceptional.DeletedEightFaithful", "any"), ("Atlas.Comparisons.Exceptional.DeletedEight.quotientQuadratic", "Atlas.Comparisons.Exceptional.DeletedEight", "any"), ("Atlas.Comparisons.Exceptional.DeletedEight.quotient_finrank", "Atlas.Comparisons.Exceptional.DeletedEight", "any"), ("Atlas.Comparisons.Exceptional.DeletedEight.quotient_polar_nondegenerate", "Atlas.Comparisons.Exceptional.DeletedEightNondegenerate", "theorem"), ("Atlas.Comparisons.Exceptional.DeletedEight.splitIsometry", "Atlas.Comparisons.Exceptional.DeletedEightSplit", "any"), ("Atlas.Comparisons.Exceptional.Nine.card", "Atlas.Comparisons.Exceptional.NineCoordinates", "any"), ("Atlas.Comparisons.Exceptional.Nine.fieldEquiv", "Atlas.Comparisons.Exceptional.NineCoordinates", "any"), ("Atlas.Comparisons.Exceptional.Nine.lower_coordinates", "Atlas.Comparisons.Exceptional.PSL2NineGenerators", "any"), ("Atlas.Comparisons.Exceptional.Nine.marking", "Atlas.Comparisons.Exceptional.PSL2NineAction", "any"), ("Atlas.Comparisons.Exceptional.Nine.permutation", "Atlas.Comparisons.Exceptional.PSL2NineAction", "any"), ("Atlas.Comparisons.Exceptional.Nine.permutation_injective", "Atlas.Comparisons.Exceptional.PSL2NineAction", "any"), ("Atlas.Comparisons.Exceptional.Nine.permutation_inversion", "Atlas.Comparisons.Exceptional.PSL2NineAction", "any"), ("Atlas.Comparisons.Exceptional.Nine.permutation_omega", "Atlas.Comparisons.Exceptional.PSL2NineAction", "any"), ("Atlas.Comparisons.Exceptional.Nine.permutation_upper", "Atlas.Comparisons.Exceptional.PSL2NineAction", "any"), ("Atlas.Comparisons.Exceptional.Nine.psl_generated", "Atlas.Comparisons.Exceptional.PSL2NineGenerators", "any"), ("Atlas.Comparisons.Exceptional.Nine.sl_generated", "Atlas.Comparisons.Exceptional.PSL2NineGenerators", "any"), ("Atlas.Comparisons.Exceptional.Nine.upper_coordinates", "Atlas.Comparisons.Exceptional.PSL2NineGenerators", "any"), ("Atlas.Comparisons.Exceptional.TriplePartitions.action", "Atlas.Comparisons.Exceptional.TriplePartitions", "any"), ("Atlas.Comparisons.Exceptional.TriplePartitions.action_doubleSwap", "Atlas.Comparisons.Exceptional.TriplePartitions", "any"), ("Atlas.Comparisons.Exceptional.TriplePartitions.action_firstCycle", "Atlas.Comparisons.Exceptional.TriplePartitions", "any"), ("Atlas.Comparisons.Exceptional.TriplePartitions.action_injective", "Atlas.Comparisons.Exceptional.TriplePartitions", "any"), ("Atlas.Comparisons.Exceptional.TriplePartitions.action_secondCycle", "Atlas.Comparisons.Exceptional.TriplePartitions", "any"), ("Atlas.Comparisons.Exceptional.TriplePartitions.marking", "Atlas.Comparisons.Exceptional.TriplePartitions", "any"), ("Atlas.Comparisons.Exceptional.TriplePartitions.partition_card", "Atlas.Comparisons.Exceptional.TriplePartitions", "any"), ("Atlas.Comparisons.Exceptional.alt6_card", "Atlas.Comparisons.Exceptional.Order360", "any"), ("Atlas.Comparisons.Exceptional.alt8EquivD3Two", "Atlas.Comparisons.Exceptional.Order20160A8", "any"), ("Atlas.Comparisons.Exceptional.alt8_card", "Atlas.Comparisons.Exceptional.Order20160A8", "any"), ("Atlas.Comparisons.Exceptional.alt8_card_eq_psl3Card4", "Atlas.Comparisons.Exceptional.Order20160Nonisomorphism", "theorem"), ("Atlas.Comparisons.Exceptional.alt8_not_equiv_psl3Card4", "Atlas.Comparisons.Exceptional.Order20160Nonisomorphism", "theorem"), ("Atlas.Comparisons.Exceptional.b2BinaryDerivedEquivC2Derived", "Atlas.Comparisons.Exceptional.BinaryDerived", "any"), ("Atlas.Comparisons.Exceptional.b2BinaryDerivedEquivC2Derived_coe", "Atlas.Comparisons.Exceptional.BinaryDerived", "any"), ("Atlas.Comparisons.Exceptional.c2BinaryDerivedEquivAlt6", "Atlas.Comparisons.Exceptional.BinaryDerived", "any"), ("Atlas.Comparisons.Exceptional.c2BinaryDerivedEquivAlt6_coherence", "Atlas.Comparisons.Exceptional.BinaryDerived", "any"), ("Atlas.Comparisons.Exceptional.cardFourFieldEquiv", "Atlas.Comparisons.Exceptional.Order60Four", "any"), ("Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5", "Atlas.Comparisons.Exceptional.Order60Four", "any"), ("Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5_action", "Atlas.Comparisons.Exceptional.Order60Four", "theorem"), ("Atlas.Comparisons.Exceptional.psl2Card4EquivPsl2Five", "Atlas.Comparisons.Exceptional.Order60Five", "any"), ("Atlas.Comparisons.Exceptional.psl2Card4RecognitionEquivAlt5", "Atlas.Comparisons.Exceptional.Order60Five", "any"), ("Atlas.Comparisons.Exceptional.psl2Card5EquivAlt5", "Atlas.Comparisons.Exceptional.Order60Five", "any"), ("Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6", "Atlas.Comparisons.Exceptional.Order360", "any"), ("Atlas.Comparisons.Exceptional.psl2Card9EquivB2BinaryDerived", "Atlas.Comparisons.Exceptional.Order360", "any"), ("Atlas.Comparisons.Exceptional.psl2Card9EquivC2BinaryDerived", "Atlas.Comparisons.Exceptional.Order360", "any"), ("Atlas.Comparisons.Exceptional.psl2Card9_card", "Atlas.Comparisons.Exceptional.Order360", "any"), ("Atlas.Comparisons.Exceptional.psl2FiveEquivAlt5", "Atlas.Comparisons.Exceptional.Order60Five", "any"), ("Atlas.Comparisons.Exceptional.psl2FourEquivAlt5", "Atlas.Comparisons.Exceptional.Order60Four", "any"), ("Atlas.Comparisons.Exceptional.psl2FourEquivPsl2Five", "Atlas.Comparisons.Exceptional.Order60Five", "any"), ("Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6", "Atlas.Comparisons.Exceptional.Order360", "any"), ("Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6_action", "Atlas.Comparisons.Exceptional.Order360", "any"), ("Atlas.Comparisons.Exceptional.psl2NineEquivAlt6", "Atlas.Comparisons.Exceptional.Order360", "any"), ("Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two", "Atlas.Comparisons.Exceptional.Order168", "any"), ("Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two", "Atlas.Comparisons.Exceptional.Order168", "any"), ("Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two_action", "Atlas.Comparisons.Exceptional.Order168", "theorem"), ("Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8", "Atlas.Comparisons.Exceptional.Order20160A8", "any"), ("Atlas.Comparisons.Exceptional.psl4Two_card", "Atlas.Comparisons.Exceptional.Order20160A8", "any"), ("Atlas.Comparisons.Exceptional.psl4Two_card_eq_psl3Card4", "Atlas.Comparisons.Exceptional.Order20160Nonisomorphism", "theorem"), ("Atlas.Comparisons.Exceptional.psl4Two_not_equiv_psl3Card4", "Atlas.Comparisons.Exceptional.Order20160Nonisomorphism", "theorem"), ("Atlas.GroupTheory.commutatorEquiv", "Atlas.GroupTheory.CommutatorEquiv", "any"), ("Atlas.GroupTheory.commutatorEquiv_coe", "Atlas.GroupTheory.CommutatorEquiv", "any"), ("Atlas.GroupTheory.not_mulEquiv_of_sylow_center_card_ne", "Atlas.GroupTheory.SylowCenterInvariant", "any"), ("Atlas.GroupTheory.smallSimpleOrder60EquivAlt5", "Atlas.GroupTheory.SimpleOrderSixty", "any"), ("Atlas.GroupTheory.sylowCenterEquiv", "Atlas.GroupTheory.SylowCenterInvariant", "any"), ("Atlas.GroupTheory.sylowEquivOfMulEquiv", "Atlas.GroupTheory.SylowCenterInvariant", "any"), ("Atlas.LinearGroups.UnitriangularFour.card", "Atlas.LinearGroups.UpperUnitriangularFour", "any"), ("Atlas.LinearGroups.UnitriangularFour.centerEquiv", "Atlas.LinearGroups.UpperUnitriangularFour", "any"), ("Atlas.LinearGroups.UnitriangularFour.center_card", "Atlas.LinearGroups.UpperUnitriangularFour", "any"), ("Atlas.LinearGroups.UnitriangularFour.member_center_iff", "Atlas.LinearGroups.UpperUnitriangularFour", "any"), ("Atlas.LinearGroups.UnitriangularFour.projective_injective", "Atlas.LinearGroups.UnitriangularFourProjective", "any"), ("Atlas.LinearGroups.UnitriangularFour.sylowModelEquiv", "Atlas.LinearGroups.UnitriangularFourProjective", "any"), ("Atlas.LinearGroups.UnitriangularFour.sylowTwo", "Atlas.LinearGroups.UnitriangularFourProjective", "any"), ("Atlas.LinearGroups.UnitriangularFour.sylowTwo_card", "Atlas.LinearGroups.UnitriangularFourProjective", "any"), ("Atlas.LinearGroups.UnitriangularFour.sylowTwo_center_card", "Atlas.LinearGroups.UnitriangularFourProjective", "any"), ("Atlas.LinearGroups.UnitriangularThree.card", "Atlas.LinearGroups.UpperUnitriangularThree", "any"), ("Atlas.LinearGroups.UnitriangularThree.centerEquiv", "Atlas.LinearGroups.UpperUnitriangularThree", "any"), ("Atlas.LinearGroups.UnitriangularThree.center_card", "Atlas.LinearGroups.UpperUnitriangularThree", "any"), ("Atlas.LinearGroups.UnitriangularThree.member_center_iff", "Atlas.LinearGroups.UpperUnitriangularThree", "any"), ("Atlas.LinearGroups.UnitriangularThree.projective_injective", "Atlas.LinearGroups.UnitriangularThreeProjective", "any"), ("Atlas.LinearGroups.UnitriangularThree.sylowModelEquiv", "Atlas.LinearGroups.UnitriangularThreeProjective", "any"), ("Atlas.LinearGroups.UnitriangularThree.sylowTwo", "Atlas.LinearGroups.UnitriangularThreeProjective", "any"), ("Atlas.LinearGroups.UnitriangularThree.sylowTwo_card", "Atlas.LinearGroups.UnitriangularThreeProjective", "any"), ("Atlas.LinearGroups.UnitriangularThree.sylowTwo_center_card", "Atlas.LinearGroups.UnitriangularThreeProjective", "any"), ("Atlas.fieldEquivPSL", "Atlas.LinearGroups.PSLFieldTransport", "any"), ("Atlas.fieldEquivPSL_projection", "Atlas.LinearGroups.PSLFieldTransport", "theorem"), ("Atlas.fieldEquivSL", "Atlas.LinearGroups.PSLFieldTransport", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/orthogonal-comparison-contracts/20260915T124053-3"
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
