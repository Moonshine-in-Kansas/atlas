import Atlas.LinearGroups.SuzukiFamily.BruhatRewrite
import Atlas.LinearGroups.SuzukiFamily.ProjectiveAction
import Atlas.LinearGroups.SuzukiFamily.RootPointAction
import Atlas.LinearGroups.SuzukiFamily.WeylPointAction
import Atlas.LinearGroups.SuzukiFamily.TorusPointAction
import Atlas.LinearGroups.SuzukiFamily.GlobalPointAction
import Atlas.LinearGroups.SuzukiFamily.GroupRelations
import Atlas.LinearGroups.SuzukiFamily.NormalForms
import Atlas.LinearGroups.SuzukiFamily.Commutation
import Atlas.LinearGroups.SuzukiFamily.CellClosure
import Atlas.LinearGroups.SuzukiFamily.Bruhat
import Atlas.LinearGroups.SuzukiFamily.PointTransitivity
import Atlas.LinearGroups.SuzukiFamily.ExactStabilizer
import Atlas.LinearGroups.SuzukiFamily.RootSolvable
import Atlas.LinearGroups.SuzukiFamily.Borel
import Atlas.LinearGroups.SuzukiFamily.BorelSolvable
import Atlas.LinearGroups.SuzukiFamily.SplitBorel
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.SuzukiFamily.CellParameters", "Atlas.LinearGroups.SuzukiFamily.Bruhat", "any"), ("Atlas.SuzukiFamily.HasForm", "Atlas.LinearGroups.SuzukiFamily.CellClosure", "any"), ("Atlas.SuzukiFamily.borel", "Atlas.LinearGroups.SuzukiFamily.Borel", "any"), ("Atlas.SuzukiFamily.borelParameters", "Atlas.LinearGroups.SuzukiFamily.Borel", "any"), ("Atlas.SuzukiFamily.borelParameters_symm_short", "Atlas.LinearGroups.SuzukiFamily.BorelSolvable", "any"), ("Atlas.SuzukiFamily.borelProjection", "Atlas.LinearGroups.SuzukiFamily.BorelSolvable", "any"), ("Atlas.SuzukiFamily.borelProjection_ker_eq_root", "Atlas.LinearGroups.SuzukiFamily.BorelSolvable", "any"), ("Atlas.SuzukiFamily.borelProjection_section", "Atlas.LinearGroups.SuzukiFamily.SplitBorel", "any"), ("Atlas.SuzukiFamily.borelProjection_short", "Atlas.LinearGroups.SuzukiFamily.BorelSolvable", "any"), ("Atlas.SuzukiFamily.borelProjection_surjective", "Atlas.LinearGroups.SuzukiFamily.BorelSolvable", "any"), ("Atlas.SuzukiFamily.borelTorusHom", "Atlas.LinearGroups.SuzukiFamily.SplitBorel", "any"), ("Atlas.SuzukiFamily.borelTorusHom_injective", "Atlas.LinearGroups.SuzukiFamily.SplitBorel", "any"), ("Atlas.SuzukiFamily.borel_solvable", "Atlas.LinearGroups.SuzukiFamily.BorelSolvable", "any"), ("Atlas.SuzukiFamily.bruhatTorus", "Atlas.LinearGroups.SuzukiFamily.BruhatRewrite", "any"), ("Atlas.SuzukiFamily.card_borel", "Atlas.LinearGroups.SuzukiFamily.Borel", "any"), ("Atlas.SuzukiFamily.card_torusSubgroup", "Atlas.LinearGroups.SuzukiFamily.SplitBorel", "any"), ("Atlas.SuzukiFamily.cellEquiv", "Atlas.LinearGroups.SuzukiFamily.Bruhat", "any"), ("Atlas.SuzukiFamily.cellMap", "Atlas.LinearGroups.SuzukiFamily.Bruhat", "any"), ("Atlas.SuzukiFamily.cellMap_bijective", "Atlas.LinearGroups.SuzukiFamily.Bruhat", "any"), ("Atlas.SuzukiFamily.columnEquiv", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.fixes_infinity_iff_short", "Atlas.LinearGroups.SuzukiFamily.ExactStabilizer", "any"), ("Atlas.SuzukiFamily.fixes_two_iff_torus", "Atlas.LinearGroups.SuzukiFamily.ExactStabilizer", "any"), ("Atlas.SuzukiFamily.generated_hasForm", "Atlas.LinearGroups.SuzukiFamily.Bruhat", "any"), ("Atlas.SuzukiFamily.generated_preserves_pointSet", "Atlas.LinearGroups.SuzukiFamily.GlobalPointAction", "any"), ("Atlas.SuzukiFamily.hasForm_one", "Atlas.LinearGroups.SuzukiFamily.CellClosure", "any"), ("Atlas.SuzukiFamily.hasForm_root_left", "Atlas.LinearGroups.SuzukiFamily.CellClosure", "any"), ("Atlas.SuzukiFamily.hasForm_torus_left", "Atlas.LinearGroups.SuzukiFamily.CellClosure", "any"), ("Atlas.SuzukiFamily.hasForm_weyl_left", "Atlas.LinearGroups.SuzukiFamily.CellClosure", "any"), ("Atlas.SuzukiFamily.infinityOvoid", "Atlas.LinearGroups.SuzukiFamily.Borel", "any"), ("Atlas.SuzukiFamily.longForm", "Atlas.LinearGroups.SuzukiFamily.NormalForms", "any"), ("Atlas.SuzukiFamily.longForm_infinity", "Atlas.LinearGroups.SuzukiFamily.NormalForms", "any"), ("Atlas.SuzukiFamily.longForm_injective", "Atlas.LinearGroups.SuzukiFamily.NormalForms", "any"), ("Atlas.SuzukiFamily.longForm_mem", "Atlas.LinearGroups.SuzukiFamily.Bruhat", "any"), ("Atlas.SuzukiFamily.matrix", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.matrix_injective", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.matrix_mul", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.matrix_one", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.matrix_root", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.matrix_torus", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.matrix_weyl", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.mem_borel", "Atlas.LinearGroups.SuzukiFamily.Borel", "any"), ("Atlas.SuzukiFamily.move_pair_to_base", "Atlas.LinearGroups.SuzukiFamily.PointTransitivity", "any"), ("Atlas.SuzukiFamily.move_point_to_infinity", "Atlas.LinearGroups.SuzukiFamily.PointTransitivity", "any"), ("Atlas.SuzukiFamily.norm_reciprocal", "Atlas.LinearGroups.SuzukiFamily.BruhatRewrite", "any"), ("Atlas.SuzukiFamily.pointAction", "Atlas.LinearGroups.SuzukiFamily.GlobalPointAction", "any"), ("Atlas.SuzukiFamily.pointAction_faithful", "Atlas.LinearGroups.SuzukiFamily.ExactStabilizer", "any"), ("Atlas.SuzukiFamily.pointAction_preprimitive", "Atlas.LinearGroups.SuzukiFamily.PointTransitivity", "any"), ("Atlas.SuzukiFamily.pointAction_two_pretransitive", "Atlas.LinearGroups.SuzukiFamily.PointTransitivity", "any"), ("Atlas.SuzukiFamily.pointLeft", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.pointLeft_injective", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.pointLeft_inv_cancel", "Atlas.LinearGroups.SuzukiFamily.PointTransitivity", "any"), ("Atlas.SuzukiFamily.pointLeft_mul", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.pointLeft_one", "Atlas.LinearGroups.SuzukiFamily.ProjectiveAction", "any"), ("Atlas.SuzukiFamily.pointSetStabilizer", "Atlas.LinearGroups.SuzukiFamily.GlobalPointAction", "any"), ("Atlas.SuzukiFamily.rootCentralHom", "Atlas.LinearGroups.SuzukiFamily.RootSolvable", "any"), ("Atlas.SuzukiFamily.rootFirstHom", "Atlas.LinearGroups.SuzukiFamily.RootSolvable", "any"), ("Atlas.SuzukiFamily.rootFirst_ker_le_central", "Atlas.LinearGroups.SuzukiFamily.RootSolvable", "any"), ("Atlas.SuzukiFamily.rootIntoBorel", "Atlas.LinearGroups.SuzukiFamily.BorelSolvable", "any"), ("Atlas.SuzukiFamily.rootIntoBorel_injective", "Atlas.LinearGroups.SuzukiFamily.SplitBorel", "any"), ("Atlas.SuzukiFamily.rootSubgroup_solvable", "Atlas.LinearGroups.SuzukiFamily.RootSolvable", "any"), ("Atlas.SuzukiFamily.root_affine", "Atlas.LinearGroups.SuzukiFamily.RootPointAction", "any"), ("Atlas.SuzukiFamily.root_affine_vector", "Atlas.LinearGroups.SuzukiFamily.RootPointAction", "any"), ("Atlas.SuzukiFamily.root_infinity", "Atlas.LinearGroups.SuzukiFamily.RootPointAction", "any"), ("Atlas.SuzukiFamily.root_infinity_vector", "Atlas.LinearGroups.SuzukiFamily.RootPointAction", "any"), ("Atlas.SuzukiFamily.root_origin", "Atlas.LinearGroups.SuzukiFamily.PointTransitivity", "any"), ("Atlas.SuzukiFamily.root_torus_swap", "Atlas.LinearGroups.SuzukiFamily.Commutation", "any"), ("Atlas.SuzukiFamily.shortForm", "Atlas.LinearGroups.SuzukiFamily.NormalForms", "any"), ("Atlas.SuzukiFamily.shortForm_infinity", "Atlas.LinearGroups.SuzukiFamily.NormalForms", "any"), ("Atlas.SuzukiFamily.shortForm_injective", "Atlas.LinearGroups.SuzukiFamily.NormalForms", "any"), ("Atlas.SuzukiFamily.shortForm_mem", "Atlas.LinearGroups.SuzukiFamily.Bruhat", "any"), ("Atlas.SuzukiFamily.shortForm_origin", "Atlas.LinearGroups.SuzukiFamily.ExactStabilizer", "any"), ("Atlas.SuzukiFamily.shortInBorel", "Atlas.LinearGroups.SuzukiFamily.Borel", "any"), ("Atlas.SuzukiFamily.shortInBorel_bijective", "Atlas.LinearGroups.SuzukiFamily.Borel", "any"), ("Atlas.SuzukiFamily.shortInBorel_mul", "Atlas.LinearGroups.SuzukiFamily.Borel", "any"), ("Atlas.SuzukiFamily.shortInBorel_zero_one", "Atlas.LinearGroups.SuzukiFamily.BorelSolvable", "any"), ("Atlas.SuzukiFamily.short_ne_long", "Atlas.LinearGroups.SuzukiFamily.NormalForms", "any"), ("Atlas.SuzukiFamily.torusElement_injective", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.torusElement_inv", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.torusElement_mul", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.torusElement_one", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.torusHom", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.torusParameters", "Atlas.LinearGroups.SuzukiFamily.SplitBorel", "any"), ("Atlas.SuzukiFamily.torusSubgroup", "Atlas.LinearGroups.SuzukiFamily.SplitBorel", "any"), ("Atlas.SuzukiFamily.torus_affine", "Atlas.LinearGroups.SuzukiFamily.TorusPointAction", "any"), ("Atlas.SuzukiFamily.torus_affine_vector", "Atlas.LinearGroups.SuzukiFamily.TorusPointAction", "any"), ("Atlas.SuzukiFamily.torus_infinity", "Atlas.LinearGroups.SuzukiFamily.TorusPointAction", "any"), ("Atlas.SuzukiFamily.torus_root_conjugate", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.torus_root_injective", "Atlas.LinearGroups.SuzukiFamily.NormalForms", "any"), ("Atlas.SuzukiFamily.torus_root_swap", "Atlas.LinearGroups.SuzukiFamily.Commutation", "any"), ("Atlas.SuzukiFamily.torus_weyl_swap", "Atlas.LinearGroups.SuzukiFamily.Commutation", "any"), ("Atlas.SuzukiFamily.weylElement_inv", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.weylElement_square", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.weyl_affine", "Atlas.LinearGroups.SuzukiFamily.WeylPointAction", "any"), ("Atlas.SuzukiFamily.weyl_affine_vector", "Atlas.LinearGroups.SuzukiFamily.WeylPointAction", "any"), ("Atlas.SuzukiFamily.weyl_infinity", "Atlas.LinearGroups.SuzukiFamily.WeylPointAction", "any"), ("Atlas.SuzukiFamily.weyl_infinity_vector", "Atlas.LinearGroups.SuzukiFamily.WeylPointAction", "any"), ("Atlas.SuzukiFamily.weyl_origin", "Atlas.LinearGroups.SuzukiFamily.WeylPointAction", "any"), ("Atlas.SuzukiFamily.weyl_root_rewrite", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any"), ("Atlas.SuzukiFamily.weyl_root_weyl", "Atlas.LinearGroups.SuzukiFamily.BruhatRewrite", "any"), ("Atlas.SuzukiFamily.weyl_torus_weyl", "Atlas.LinearGroups.SuzukiFamily.GroupRelations", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "verification/runs/suzuki-family-structure/20260927T025635-4"
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
