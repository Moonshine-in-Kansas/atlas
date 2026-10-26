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
  let rootSpecs : Array (String × String × String) := #[("Atlas.G2.OrderChecks.binary_order", "Atlas.LinearGroups.G2.OrderChecks", "any"), ("Atlas.G2.OrderChecks.binary_points", "Atlas.LinearGroups.G2.OrderChecks", "any"), ("Atlas.G2.OrderChecks.eight_order", "Atlas.LinearGroups.G2.OrderChecks", "any"), ("Atlas.G2.OrderChecks.five_order", "Atlas.LinearGroups.G2.OrderChecks", "any"), ("Atlas.G2.OrderChecks.four_order", "Atlas.LinearGroups.G2.OrderChecks", "any"), ("Atlas.G2.OrderChecks.four_points", "Atlas.LinearGroups.G2.OrderChecks", "any"), ("Atlas.G2.OrderChecks.ternary_order", "Atlas.LinearGroups.G2.OrderChecks", "any"), ("Atlas.G2.OrderChecks.ternary_points", "Atlas.LinearGroups.G2.OrderChecks", "any"), ("Atlas.G2.PairStabilizer.fixingPair", "Atlas.LinearGroups.G2.PairStabilizer", "any"), ("Atlas.G2.PairStabilizer.fixingPairEquivSL2", "Atlas.LinearGroups.G2.PairStabilizer", "any"), ("Atlas.G2.SingularPoints", "Atlas.LinearGroups.G2.SingularPoints", "any"), ("Atlas.G2.borelProductEquiv", "Atlas.LinearGroups.G2.Borel", "any"), ("Atlas.G2.borel_relIndex_parabolic", "Atlas.LinearGroups.G2.Parabolic", "any"), ("Atlas.G2.card_Model", "Atlas.LinearGroups.G2.Order", "any"), ("Atlas.G2.card_Model_eq_points_mul_stabilizer", "Atlas.LinearGroups.G2.Order", "any"), ("Atlas.G2.card_borel", "Atlas.LinearGroups.G2.Borel", "any"), ("Atlas.G2.card_fixingFirstVector_SL2", "Atlas.LinearGroups.G2.VectorStabilizer", "any"), ("Atlas.G2.card_fixingFirstVector_formula", "Atlas.LinearGroups.G2.Order", "any"), ("Atlas.G2.card_nonzeroSingularOctonions", "Atlas.LinearGroups.G2.SingularOctonions", "any"), ("Atlas.G2.card_parabolic", "Atlas.LinearGroups.G2.Parabolic", "any"), ("Atlas.G2.card_pointStabilizer_formula", "Atlas.LinearGroups.G2.Order", "any"), ("Atlas.G2.card_singularPoints", "Atlas.LinearGroups.G2.SingularPoints", "any"), ("Atlas.G2.card_singularPoints_sum", "Atlas.LinearGroups.G2.SingularPoints", "any"), ("Atlas.G2.card_splitTorus", "Atlas.LinearGroups.G2.Torus", "any"), ("Atlas.G2.card_unipotent", "Atlas.LinearGroups.G2.Unipotent", "any"), ("Atlas.G2.exists_mul_ne_mul", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.exists_smul_firstPoint", "Atlas.LinearGroups.G2.PointStabilizer", "any"), ("Atlas.G2.firstPoint", "Atlas.LinearGroups.G2.PointStabilizer", "any"), ("Atlas.G2.fixingFirstVector", "Atlas.LinearGroups.G2.VectorStabilizer", "any"), ("Atlas.G2.fixingFirstVectorEquivPartners", "Atlas.LinearGroups.G2.VectorStabilizer", "any"), ("Atlas.G2.generated", "Atlas.LinearGroups.G2.Generation", "any"), ("Atlas.G2.generated_eq_top", "Atlas.LinearGroups.G2.Generation", "any"), ("Atlas.G2.lineScalarHom", "Atlas.LinearGroups.G2.PointStabilizer", "any"), ("Atlas.G2.lineScalarHom_kernel", "Atlas.LinearGroups.G2.PointStabilizer", "any"), ("Atlas.G2.lineScalarHom_surjective", "Atlas.LinearGroups.G2.PointStabilizer", "any"), ("Atlas.G2.nonzeroSingularEquivPointsUnits", "Atlas.LinearGroups.G2.SingularPoints", "any"), ("Atlas.G2.nonzeroSingularOctonionsEquivCoordinates", "Atlas.LinearGroups.G2.SingularOctonions", "any"), ("Atlas.G2.parabolic", "Atlas.LinearGroups.G2.Parabolic", "any"), ("Atlas.G2.parabolicNormalForm", "Atlas.LinearGroups.G2.Parabolic", "any"), ("Atlas.G2.parabolic_eq_pointStabilizer", "Atlas.LinearGroups.G2.Parabolic", "any"), ("Atlas.G2.pointStabilizer", "Atlas.LinearGroups.G2.PointStabilizer", "any"), ("Atlas.G2.pointStabilizerEquiv", "Atlas.LinearGroups.G2.PointStabilizer", "any"), ("Atlas.G2.rootA", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootA_add", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootA_injective", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootB", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootB_add", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootB_injective", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootC", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootC_add", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootC_injective", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootD", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootD_add", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootD_injective", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootE", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootE_add", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootE_injective", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootF", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootF_add", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.rootF_injective", "Atlas.LinearGroups.G2.RootGroups", "any"), ("Atlas.G2.singularOctonionsEquivCoordinates", "Atlas.LinearGroups.G2.SingularOctonions", "any"), ("Atlas.G2.singularPointMk", "Atlas.LinearGroups.G2.SingularPoints", "any"), ("Atlas.G2.singularPointsAction", "Atlas.LinearGroups.G2.SingularAction", "any"), ("Atlas.G2.singularPointsFaithful", "Atlas.LinearGroups.G2.SingularAction", "any"), ("Atlas.G2.singularPoints_pretransitive", "Atlas.LinearGroups.G2.PointStabilizer", "any"), ("Atlas.G2.singular_lines_kernel_trivial", "Atlas.LinearGroups.G2.SingularAction", "any"), ("Atlas.G2.singular_vector_reduction_first", "Atlas.LinearGroups.G2.SingularReduction", "any"), ("Atlas.G2.torus", "Atlas.LinearGroups.G2.Torus", "any"), ("Atlas.G2.torusHom", "Atlas.LinearGroups.G2.Torus", "any"), ("Atlas.G2.torusHom_injective", "Atlas.LinearGroups.G2.Torus", "any"), ("Atlas.G2.torusParameterEquiv", "Atlas.LinearGroups.G2.Torus", "any"), ("Atlas.G2.torus_normalizes_unipotent", "Atlas.LinearGroups.G2.Borel", "any"), ("Atlas.G2.torus_rootA", "Atlas.LinearGroups.G2.TorusNormalization", "any"), ("Atlas.G2.torus_rootB", "Atlas.LinearGroups.G2.TorusNormalization", "any"), ("Atlas.G2.torus_rootC", "Atlas.LinearGroups.G2.TorusNormalization", "any"), ("Atlas.G2.torus_rootD", "Atlas.LinearGroups.G2.TorusNormalization", "any"), ("Atlas.G2.torus_rootE", "Atlas.LinearGroups.G2.TorusNormalization", "any"), ("Atlas.G2.torus_rootF", "Atlas.LinearGroups.G2.TorusNormalization", "any"), ("Atlas.G2.torus_unipotentProduct", "Atlas.LinearGroups.G2.TorusNormalization", "any"), ("Atlas.G2.unipotentEquiv", "Atlas.LinearGroups.G2.Unipotent", "any"), ("Atlas.G2.unipotentParameters_product", "Atlas.LinearGroups.G2.Unipotent", "any"), ("Atlas.G2.unipotentProduct", "Atlas.LinearGroups.G2.Unipotent", "any"), ("Atlas.G2.unipotentProduct_inv", "Atlas.LinearGroups.G2.Unipotent", "any"), ("Atlas.G2.unipotentProduct_mul", "Atlas.LinearGroups.G2.Unipotent", "any"), ("Atlas.G2.unipotent_disjoint_torus", "Atlas.LinearGroups.G2.Borel", "any"), ("Atlas.G2.unipotent_eq_range", "Atlas.LinearGroups.G2.Unipotent", "any"), ("Atlas.G2.weylR", "Atlas.LinearGroups.G2.WeylMaps", "any"), ("Atlas.G2.weylR_sq", "Atlas.LinearGroups.G2.WeylMaps", "any"), ("Atlas.G2.weylS", "Atlas.LinearGroups.G2.WeylMaps", "any"), ("Atlas.G2.weylS_sq", "Atlas.LinearGroups.G2.WeylMaps", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/g2-order/20260916T025914-3"
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
