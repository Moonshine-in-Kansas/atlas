import Atlas.Comparisons.Exceptional.G2Binary.Derived
import Atlas.Comparisons.Exceptional.G2Binary.FieldNineOrder
import Atlas.Comparisons.Exceptional.G2Binary.FieldTransport
import Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration
import Atlas.Comparisons.Exceptional.G2Binary.OctonionWords
import Atlas.Comparisons.Exceptional.G2Binary.QuadraticAction
import Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful
import Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints
import Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity
import Atlas.Comparisons.Exceptional.G2Binary.Simplicity
import Atlas.Comparisons.Exceptional.G2Binary.SplitExtension
import Atlas.GroupTheory.PerfectNormalClosureIwasawa
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
  let rootSpecs : Array (String × String × String) := #[("Atlas.Comparisons.G2Binary.Final6048.card_fieldNine_psu", "Atlas.Comparisons.Exceptional.G2Binary.FieldNineOrder", "theorem"), ("Atlas.Comparisons.G2Binary.IsQuadraticRoot", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.Matching6048.act4", "Atlas.Comparisons.Exceptional.G2Binary.OctonionWords", "definition"), ("Atlas.Comparisons.G2Binary.Matching6048.element4", "Atlas.Comparisons.Exceptional.G2Binary.OctonionWords", "definition"), ("Atlas.Comparisons.G2Binary.Matching6048.element4_apply", "Atlas.Comparisons.Exceptional.G2Binary.OctonionWords", "theorem"), ("Atlas.Comparisons.G2Binary.Matching6048.element4_mem", "Atlas.Comparisons.Exceptional.G2Binary.OctonionWords", "theorem"), ("Atlas.Comparisons.G2Binary.Matching6048.step4", "Atlas.Comparisons.Exceptional.G2Binary.OctonionWords", "definition"), ("Atlas.Comparisons.G2Binary.Matching6048.word4", "Atlas.Comparisons.Exceptional.G2Binary.OctonionWords", "definition"), ("Atlas.Comparisons.G2Binary.Matching6048.word4_apply", "Atlas.Comparisons.Exceptional.G2Binary.OctonionWords", "theorem"), ("Atlas.Comparisons.G2Binary.Matching6048.word4_mem", "Atlas.Comparisons.Exceptional.G2Binary.OctonionWords", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.Lines", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.Projective", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.Special", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.binaryMarking", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.binaryPoint", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.binaryPoint_surjective", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.binaryRepresentation", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.binaryRepresentation_apply", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.binaryRepresentation_injective", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.card_lines", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.imaginary_trace_zero", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.markedLine", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.markedLineGroup_eq_zpowers", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.markedLine_injective", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.markedPointGroup_eq_zpowers", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.markedVector_isotropic", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.markedVector_ne_zero", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.projectiveRoot", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.projectiveRoots_generate", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.rootPermutation", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.rootPermutation_apply", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.specialRoot", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.specialRoot_apply", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.specialRoot_on_lines", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.specialRoots_generate", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.unitaryImage_generated", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.unitaryMarking", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.unitaryRepresentation", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "definition"), ("Atlas.Comparisons.G2Binary.Source6048.unitaryRepresentation_apply", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.Source6048.unitaryRepresentation_injective", "Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration", "theorem"), ("Atlas.Comparisons.G2Binary.automorphism_partner", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticAction", "any"), ("Atlas.Comparisons.G2Binary.automorphism_root", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticAction", "any"), ("Atlas.Comparisons.G2Binary.basePoint", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.baseVector", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.binary_geometry", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.card_quadraticPoint", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.card_quadraticRoot", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.exists_word_to_point", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.longRoot_quadraticPoint_transitive", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.markedVector", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.markedWord", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.marking_complete", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.normalize", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.normalize_automorphism_normalize", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticAction", "any"), ("Atlas.Comparisons.G2Binary.normalize_cases", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.normalize_eq_iff", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.normalize_geometry", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.normalize_partner", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.partner", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.partner_add_both", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful", "any"), ("Atlas.Comparisons.G2Binary.partner_add_left", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful", "any"), ("Atlas.Comparisons.G2Binary.partner_add_right", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful", "any"), ("Atlas.Comparisons.G2Binary.partner_involutive", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.partner_ne", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.partner_root", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.pointKernel_root", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful", "any"), ("Atlas.Comparisons.G2Binary.pointKernel_traceZero", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful", "any"), ("Atlas.Comparisons.G2Binary.pointOfRoot", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.quadraticPointAction", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticAction", "any"), ("Atlas.Comparisons.G2Binary.quadraticPointRepresentation", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticAction", "any"), ("Atlas.Comparisons.G2Binary.quadraticPoint_action_eq_iff", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticAction", "any"), ("Atlas.Comparisons.G2Binary.quadraticPoint_faithful", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful", "any"), ("Atlas.Comparisons.G2Binary.root_quadratic_identity", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints", "any"), ("Atlas.Comparisons.G2Binary.step", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.stepElement", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.stepElement_apply", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.stepElement_mem", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.traceZero_partner_norm", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful", "any"), ("Atlas.Comparisons.G2Binary.traceZero_root_difference", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful", "any"), ("Atlas.Comparisons.G2Binary.wordAction", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.wordElement", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.wordElement_apply", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.Comparisons.G2Binary.wordElement_mem", "Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity", "any"), ("Atlas.G2.BinaryException.H_complement", "Atlas.Comparisons.Exceptional.G2Binary.SplitExtension", "any"), ("Atlas.G2.BinaryException.H_minimal_normal", "Atlas.Comparisons.Exceptional.G2Binary.Simplicity", "any"), ("Atlas.G2.BinaryException.H_simple", "Atlas.Comparisons.Exceptional.G2Binary.Simplicity", "any"), ("Atlas.G2.BinaryException.binarySplitExtension", "Atlas.Comparisons.Exceptional.G2Binary.SplitExtension", "any"), ("Atlas.G2.BinaryException.card_commutator", "Atlas.Comparisons.Exceptional.G2Binary.Derived", "any"), ("Atlas.G2.BinaryException.commutator_eq_H", "Atlas.Comparisons.Exceptional.G2Binary.Derived", "any"), ("Atlas.G2.BinaryException.commutator_eq_lineSign_kernel", "Atlas.Comparisons.Exceptional.G2Binary.Derived", "any"), ("Atlas.G2.BinaryException.commutator_simple", "Atlas.Comparisons.Exceptional.G2Binary.Simplicity", "any"), ("Atlas.G2.BinaryException.index_commutator", "Atlas.Comparisons.Exceptional.G2Binary.Derived", "any"), ("Atlas.G2.BinaryException.shortRootComplement", "Atlas.Comparisons.Exceptional.G2Binary.SplitExtension", "any"), ("Atlas.G2.BinaryException.shortRootComplementEquivSigns", "Atlas.Comparisons.Exceptional.G2Binary.SplitExtension", "any"), ("Atlas.G2.BinaryException.shortRootComplement_sign_bijective", "Atlas.Comparisons.Exceptional.G2Binary.SplitExtension", "any"), ("Atlas.G2.commutator_card_binary", "Atlas.Comparisons.Exceptional.G2Binary.FieldTransport", "any"), ("Atlas.G2.commutator_eq_longRootNormalClosure_binary", "Atlas.Comparisons.Exceptional.G2Binary.FieldTransport", "any"), ("Atlas.G2.commutator_index_binary", "Atlas.Comparisons.Exceptional.G2Binary.FieldTransport", "any"), ("Atlas.G2.commutator_nonabelian_binary", "Atlas.Comparisons.Exceptional.G2Binary.FieldTransport", "any"), ("Atlas.G2.commutator_perfect_binary", "Atlas.Comparisons.Exceptional.G2Binary.FieldTransport", "any"), ("Atlas.G2.commutator_simple_binary", "Atlas.Comparisons.Exceptional.G2Binary.FieldTransport", "any"), ("Atlas.G2.longRootNormalClosure_perfect", "Atlas.Comparisons.Exceptional.G2Binary.Derived", "any"), ("Atlas.G2.longRootNormalClosure_simple_binary", "Atlas.Comparisons.Exceptional.G2Binary.FieldTransport", "any"), ("Atlas.GroupTheory.commutator_normal_sup_abelian_le", "Atlas.GroupTheory.PerfectNormalClosureIwasawa", "any"), ("Atlas.GroupTheory.normalClosure_le_normal_sup_local", "Atlas.GroupTheory.PerfectNormalClosureIwasawa", "any"), ("Atlas.GroupTheory.perfect_normalClosure_minimal", "Atlas.GroupTheory.PerfectNormalClosureIwasawa", "any")]
  let roots := rootSpecs.map (fun r => r.1.toName)
  let outDir : String := "/home/gerald/atlas/claude/release-update-v1.2-20261030/verification-runs/20261030T092847-audit-batch-batch-006-g2-binary"
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
