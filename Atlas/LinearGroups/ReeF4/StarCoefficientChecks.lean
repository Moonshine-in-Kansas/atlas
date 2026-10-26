import Atlas.LinearGroups.ReeF4.StarExtensionCandidate

/-! Checks on the complete candidate coefficient table. These do not yet prove
that the candidate satisfies the full Ree generator-preservation conditions. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CharP F 2] [CommRing R] [CharP R 2]

theorem extensionCoefficient_map (f : F →+* R) (i j : TraceZeroCoordinate) :
    traceZeroMap f (extensionCoefficient i j) = extensionCoefficient i j := by
  cases i <;> cases j <;> simp only [extensionCoefficient] <;>
    (try split_ifs) <;> simp [traceZeroMap_zero, diagonalVector_map, rootVector_map,
      oppositeLabelValue_map]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check all 26-by-26 coefficient symmetries by ordinary kernel reduction.
private theorem coefficient_comm_binary : ∀ i j : TraceZeroCoordinate,
    extensionCoefficient (F := ZMod 2) i j = extensionCoefficient j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 4096 in
private theorem coefficient_self_binary : ∀ i : TraceZeroCoordinate,
    extensionCoefficient (F := ZMod 2) i i = 0 := by
  intro i
  fin_cases i <;> decide

theorem extensionCoefficient_comm (i j : TraceZeroCoordinate) :
    extensionCoefficient (F := F) i j = extensionCoefficient j i := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroMap f) (coefficient_comm_binary i j)
  simpa only [extensionCoefficient_map] using h

theorem extensionCoefficient_self (i : TraceZeroCoordinate) :
    extensionCoefficient (F := F) i i = 0 := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroMap f) (coefficient_self_binary i)
  simpa only [extensionCoefficient_map, traceZeroMap_zero] using h

private theorem perpendicular_not_opposite : ∀ r s : ShortRootLabel,
    rootDot (scaledShortRoot r) (scaledShortRoot s) = 0 → s ≠ (r.1, Fin.rev r.2) := by
  decide

theorem extensionCoefficient_perpendicular (r s : ShortRootLabel)
    (h : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    extensionCoefficient (F := F) (.inr r) (.inr s) = rootVector (starRootTarget r s) := by
  simp [extensionCoefficient, perpendicular_not_opposite r s h, h]

theorem extensionCoefficient_opposite (r : ShortRootLabel) :
    extensionCoefficient (F := F) (.inr r) (.inr (r.1, Fin.rev r.2)) = oppositeLabelValue r := by
  simp [extensionCoefficient]

theorem extensionCoefficient_opposite_pair (r s : ShortRootLabel)
    (h : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    extensionCoefficient (F := F) (.inr r) (.inr (r.1, Fin.rev r.2)) +
      extensionCoefficient (.inr s) (.inr (s.1, Fin.rev s.2)) =
        diagonalVector (starRootTarget r s).1 := by
  rw [extensionCoefficient_opposite, extensionCoefficient_opposite]
  exact oppositeLabelValue_pair r s h

end Atlas.ReeF4

