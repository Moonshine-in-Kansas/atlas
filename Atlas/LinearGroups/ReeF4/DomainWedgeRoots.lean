import Atlas.LinearGroups.ReeF4.DomainWedgeSpan

/-! Small root-system identities expressing the nondecomposable kernel
relations as sums of admissible decomposable wedges. These are local Albert
algebra identities, independent of any finite-group computation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 2048

private theorem sameBlock_no_shortSum : ∀ r s : ShortRootLabel,
    r.1 = s.1 → ∀ t : ShortRootLabel,
      scaledShortRoot r + scaledShortRoot s ≠ scaledShortRoot t := by decide

private theorem shortSum_rectangle_conditions : ∀ r s t : ShortRootLabel,
    scaledShortRoot r + scaledShortRoot s = scaledShortRoot t →
      s.1 ≠ t.1 ∧ s ≠ (r.1, Fin.rev r.2) ∧ t ≠ (r.1, Fin.rev r.2) ∧
      (∀ k : ShortRootLabel, scaledShortRoot r + scaledShortRoot t ≠ scaledShortRoot k) := by
  decide

variable {F : Type*} [CommRing F] [CharP F 2]

theorem rootDomain_sameBlock (r s : ShortRootLabel)
    (hb : r.1 = s.1) (ho : s ≠ (r.1, Fin.rev r.2)) :
    StarDomain (rootVector (F := F) r) (rootVector s) := by
  constructor
  · rw [rootPolar, if_neg ho]
  · exact rootCross_noSum r s ho (sameBlock_no_shortSum r s hb)

theorem diagonalRoot_domain (r : ShortRootLabel) :
    StarDomain (diagonalVector (F := F) r.1) (rootVector r) := by
  constructor
  · exact diagonalRootPolar r.1 r
  · simp [diagonalRootCross]

/-- A root-sum collision is resolved by one rectangle. The diagonal is the
block of the second root, so the two discarded mixed entries are admissible. -/
theorem rootSum_wedge_mem_admissibleWedgeSpan (r s t : ShortRootLabel)
    (hs : scaledShortRoot r + scaledShortRoot s = scaledShortRoot t) :
    wedge (rootVector (F := F) r) (rootVector s) +
      wedge (diagonalVector s.1) (rootVector t) ∈ admissibleWedgeSpan := by
  obtain ⟨hblock, hop, hrt, hnosum⟩ := shortSum_rectangle_conditions r s t hs
  apply collision_wedges_mem_admissibleWedgeSpan
  · rw [rootPolar, if_neg hop, diagonalRootPolar]
  · rw [rootCross_shortSum r s t hs, diagonalRootCross, if_neg hblock]
  · exact ⟨by rw [rootPolar, if_neg hrt], rootCross_noSum r t hrt hnosum⟩
  · exact diagonalRoot_domain s

/-- Opposite-pair differences in a single octonion block have a decomposable
rectangle realization. The remaining two rectangle entries are admissible. -/
theorem oppositePair_wedge_mem_admissibleWedgeSpan (r s : ShortRootLabel)
    (hb : r.1 = s.1) (hne : r.2 ≠ s.2) :
    oppositeWedge (F := F) r + oppositeWedge s ∈ admissibleWedgeSpan := by
  unfold oppositeWedge
  apply collision_wedges_mem_admissibleWedgeSpan
  · simp only [rootPolar, if_pos rfl]
  · rw [rootCross_opposite, rootCross_opposite, hb]
  · apply rootDomain_sameBlock r (s.1, Fin.rev s.2) hb
    intro h
    have hc := congrArg Prod.snd h
    have he : s.2 = r.2 := Fin.rev_injective hc
    exact hne he.symm
  · apply rootDomain_sameBlock s (r.1, Fin.rev r.2) hb.symm
    intro h
    have hc := congrArg Prod.snd h
    have he : r.2 = s.2 := Fin.rev_injective hc
    exact hne he

/-- The auxiliary diagonal in the section is immaterial modulo admissible
wedges, provided both diagonal labels act identically on this root. -/
theorem diagonalRoot_difference_mem_admissibleWedgeSpan (r : ShortRootLabel)
    (i j : Fin 3) (hi : i ≠ r.1) (hj : j ≠ r.1) :
    wedge (diagonalVector (F := F) i) (rootVector r) +
      wedge (diagonalVector j) (rootVector r) ∈ admissibleWedgeSpan := by
  have hd : StarDomain (diagonalVector (F := F) i + diagonalVector j) (rootVector r) := by
    constructor
    · rw [traceZeroPolar_add_left, diagonalRootPolar, diagonalRootPolar, add_zero]
    · rw [traceZeroCross_add_left, diagonalRootCross, diagonalRootCross,
        if_neg hi, if_neg hj, ← two_smul F, (CharTwo.two_eq_zero (R := F)), zero_smul]
  have he : wedge (diagonalVector (F := F) i + diagonalVector j) (rootVector r) =
      wedge (diagonalVector i) (rootVector r) +
        wedge (diagonalVector j) (rootVector r) :=
    (exteriorPower.ιMulti F 2).map_vecCons_add ![rootVector r]
      (diagonalVector i) (diagonalVector j)
  rw [← he]
  exact wedge_mem_admissibleWedgeSpan hd

/-- The projected short-sum relation lies in the admissible decomposable span. -/
theorem rootSum_section_wedge_mem_admissibleWedgeSpan (r s t : ShortRootLabel)
    (hs : scaledShortRoot r + scaledShortRoot s = scaledShortRoot t) :
    wedge (rootVector (F := F) r) (rootVector s) +
      wedge (diagonalVector (auxiliaryDiagonal t)) (rootVector t) ∈ admissibleWedgeSpan := by
  have ha := rootSum_wedge_mem_admissibleWedgeSpan (F := F) r s t hs
  have hb := diagonalRoot_difference_mem_admissibleWedgeSpan (F := F) t
    s.1 (auxiliaryDiagonal t) (shortSum_rectangle_conditions r s t hs).1
    (auxiliaryDiagonal_ne t)
  have h := (admissibleWedgeSpan (F := F)).add_mem ha hb
  have hzero : wedge (diagonalVector (F := F) s.1) (rootVector t) +
      wedge (diagonalVector s.1) (rootVector t) = 0 := by
    rw [← two_smul F, (CharTwo.two_eq_zero (R := F)), zero_smul]
  have he :
      (wedge (rootVector (F := F) r) (rootVector s) +
        wedge (diagonalVector s.1) (rootVector t)) +
      (wedge (diagonalVector s.1) (rootVector t) +
        wedge (diagonalVector (auxiliaryDiagonal t)) (rootVector t)) =
      wedge (rootVector r) (rootVector s) +
        wedge (diagonalVector (auxiliaryDiagonal t)) (rootVector t) := by
    calc _ = wedge (rootVector r) (rootVector s) +
          (wedge (diagonalVector s.1) (rootVector t) +
            wedge (diagonalVector s.1) (rootVector t)) +
          wedge (diagonalVector (auxiliaryDiagonal t)) (rootVector t) := by abel
      _ = _ := by rw [hzero, add_zero]
  rwa [he] at h

end Atlas.ReeF4
