import Atlas.LinearGroups.ReeF4.StarOrderedPair

/-! Evaluation of the complete candidate on actual marked-basis wedges. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem neg_eq_self_module {M : Type*} [AddCommGroup M] [Module F M] (x : M) :
    -x = x := by
  have h : x + x = 0 := by rw [← two_smul F, CharTwo.two_eq_zero, zero_smul]
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem wedge_comm_charTwo (u v : TraceZero F) : wedge u v = wedge v u := by
  have h := (exteriorPower.ιMulti F 2).map_swap ![u,v] (i := 0) (j := 1) (by decide)
  have he : ![u,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,u] := by
    funext i
    fin_cases i <;> simp
  rw [he] at h
  simpa only [wedge, neg_eq_self_module (F := F)] using h.symm

theorem proposedStarLinear_ordered_basis
    (i j : Fin (Fintype.card TraceZeroCoordinate)) :
    proposedStarLinear (wedge (orderedMarkedBasis (F := F) i) (orderedMarkedBasis j)) =
      extensionCoefficient ((Fintype.equivFin TraceZeroCoordinate).symm i)
        ((Fintype.equivFin TraceZeroCoordinate).symm j) := by
  rcases lt_trichotomy i j with h | h | h
  · exact proposedStarLinear_ordered_pair i j h
  · subst j
    have hz : wedge (orderedMarkedBasis (F := F) i) (orderedMarkedBasis i) = 0 :=
      (exteriorPower.ιMulti F 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
    rw [hz, _root_.map_zero, extensionCoefficient_self]
  · rw [wedge_comm_charTwo, proposedStarLinear_ordered_pair j i h, extensionCoefficient_comm]

theorem proposedStarLinear_marked_wedge (i j : TraceZeroCoordinate) :
    proposedStarLinear (wedge (markedBasis (F := F) i) (markedBasis j)) =
      extensionCoefficient i j := by
  have h := proposedStarLinear_ordered_basis (F := F)
    (Fintype.equivFin TraceZeroCoordinate i) (Fintype.equivFin TraceZeroCoordinate j)
  simpa [orderedMarkedBasis] using h

theorem proposedStarLinear_perpendicular (r s : ShortRootLabel)
    (h : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    proposedStarLinear (wedge (rootVector (F := F) r) (rootVector s)) =
      rootVector (starRootTarget r s) := by
  rw [← markedBasis_root r, ← markedBasis_root s, proposedStarLinear_marked_wedge]
  exact extensionCoefficient_perpendicular r s h

theorem proposedStarLinear_opposite_pair (r s : ShortRootLabel)
    (h : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    proposedStarLinear (F := F)
      (wedge (rootVector r) (rootVector (r.1, Fin.rev r.2)) +
        wedge (rootVector s) (rootVector (s.1, Fin.rev s.2))) =
      diagonalVector (starRootTarget r s).1 := by
  rw [_root_.map_add]
  simp only [← markedBasis_root, proposedStarLinear_marked_wedge]
  exact extensionCoefficient_opposite_pair r s h

end Atlas.ReeF4
