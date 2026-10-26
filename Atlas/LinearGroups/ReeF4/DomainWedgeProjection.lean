import Atlas.LinearGroups.ReeF4.DomainWedgeMissingDirection

/-! All projected marked exterior basis vectors belong to the span of actual
admissible pairs. This completes the comparison of partial-domain preservation
with preservation on the full polar/cross kernel. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private theorem neg_self_module {M : Type*} [AddCommGroup M] [Module F M] (w : M) : -w = w := by
  have h : w + w = 0 := by rw [← two_smul F, (CharTwo.two_eq_zero (R := F)), zero_smul]
  exact (eq_neg_of_add_eq_zero_left h).symm

private theorem diagonal_two_eq : diagonalVector (F := F) 2 = diagonalVector 0 + diagonalVector 1 := by
  exact (eq_neg_of_add_eq_zero_right (diagonalVector_sum (F := F))).trans
    (neg_self_module (F := F) _)

private theorem lift_root (r : ShortRootLabel) :
    exteriorLift (rootVector (F := F) r) =
      wedge (diagonalVector (auxiliaryDiagonal r)) (rootVector r) := by
  have h := (markedBasis (F := F)).constr_basis F (exteriorLiftMarked (F := F)) (.inr r)
  rw [markedBasis_root] at h
  exact h

private theorem lift_diagonal_zero : exteriorLift (diagonalVector (F := F) 0) =
    oppositeWedge (0,0) + diagonalWedge := by
  have h := (markedBasis (F := F)).constr_basis F (exteriorLiftMarked (F := F)) (.inl (0 : Fin 2))
  rw [markedBasis_diagonal] at h
  change exteriorLift (diagonalVector (Fin.castLE (by decide) (0 : Fin 2))) =
    oppositeWedge (Fin.castLE (by decide) (0 : Fin 2),0) + diagonalWedge at h
  have hi : Fin.castLE (show 2 ≤ 3 by decide) (0 : Fin 2) = (0 : Fin 3) := by decide
  simpa only [hi] using h

private theorem lift_diagonal_one : exteriorLift (diagonalVector (F := F) 1) =
    oppositeWedge (1,0) + diagonalWedge := by
  have h := (markedBasis (F := F)).constr_basis F (exteriorLiftMarked (F := F)) (.inl (1 : Fin 2))
  rw [markedBasis_diagonal] at h
  change exteriorLift (diagonalVector (Fin.castLE (by decide) (1 : Fin 2))) =
    oppositeWedge (Fin.castLE (by decide) (1 : Fin 2),0) + diagonalWedge at h
  have hi : Fin.castLE (show 2 ≤ 3 by decide) (1 : Fin 2) = (1 : Fin 3) := by decide
  simpa only [hi] using h

private theorem projection_wedge (u v : TraceZero F) :
    starProjectionLinear (wedge u v) = wedge u v -
      (traceZeroPolar u v • diagonalWedge + exteriorLift (traceZeroCross u v)) := by
  simp [starProjectionLinear, exteriorJoint, exteriorJointSection]

private theorem projection_of_mem {w : ⋀[F]^2 (TraceZero F)}
    (hw : w ∈ admissibleWedgeSpan (F := F)) : starProjectionLinear w = w :=
  congrArg Subtype.val (starProjection_of_mem
    (⟨w, admissibleWedgeSpan_le hw⟩ : StarCarrier (F := F)))

private theorem projection_mem_of_add {u v : ⋀[F]^2 (TraceZero F)}
    (huv : u + v ∈ admissibleWedgeSpan (F := F))
    (hv : starProjectionLinear v ∈ admissibleWedgeSpan (F := F)) :
    starProjectionLinear u ∈ admissibleWedgeSpan (F := F) := by
  have he := projection_of_mem huv
  rw [_root_.map_add] at he
  rw [← eq_sub_iff_add_eq] at he
  rw [he]
  exact (admissibleWedgeSpan (F := F)).sub_mem huv hv

private theorem opposite_difference_mem (r s : ShortRootLabel) (hb : r.1 = s.1) :
    oppositeWedge (F := F) r + oppositeWedge s ∈ admissibleWedgeSpan := by
  by_cases h : r.2 = s.2
  · have hrs : r = s := Prod.ext hb h
    subst s
    have hz : oppositeWedge (F := F) r + oppositeWedge r = 0 := by
      rw [← two_smul F, (CharTwo.two_eq_zero (R := F)), zero_smul]
    rw [hz]
    exact (admissibleWedgeSpan (F := F)).zero_mem
  · exact oppositePair_wedge_mem_admissibleWedgeSpan r s hb h

private theorem projection_opposite_base_zero :
    starProjectionLinear (oppositeWedge (F := F) (0,0)) = 0 := by
  rw [oppositeWedge, projection_wedge, rootPolar, if_pos rfl, rootCross_opposite,
    one_smul, lift_diagonal_zero]
  change oppositeWedge (F := F) (0,0) -
    (diagonalWedge + (oppositeWedge (0,0) + diagonalWedge)) = 0
  have hd : diagonalWedge (F := F) + diagonalWedge = 0 := by
    rw [← two_smul F, (CharTwo.two_eq_zero (R := F)), zero_smul]
  have he : diagonalWedge (F := F) + (oppositeWedge (0,0) + diagonalWedge) =
      oppositeWedge (0,0) + (diagonalWedge + diagonalWedge) := by abel
  rw [he, hd, add_zero, sub_self]

private theorem projection_opposite_base_one :
    starProjectionLinear (oppositeWedge (F := F) (1,0)) = 0 := by
  rw [oppositeWedge, projection_wedge, rootPolar, if_pos rfl, rootCross_opposite,
    one_smul, lift_diagonal_one]
  change oppositeWedge (F := F) (1,0) -
    (diagonalWedge + (oppositeWedge (1,0) + diagonalWedge)) = 0
  have hd : diagonalWedge (F := F) + diagonalWedge = 0 := by
    rw [← two_smul F, (CharTwo.two_eq_zero (R := F)), zero_smul]
  have he : diagonalWedge (F := F) + (oppositeWedge (1,0) + diagonalWedge) =
      oppositeWedge (1,0) + (diagonalWedge + diagonalWedge) := by abel
  rw [he, hd, add_zero, sub_self]

private theorem projection_opposite_base_two :
    starProjectionLinear (oppositeWedge (F := F) (2,0)) = starMissingDirection := by
  rw [oppositeWedge, projection_wedge, rootPolar, if_pos rfl, rootCross_opposite,
    one_smul, diagonal_two_eq, _root_.map_add, lift_diagonal_zero, lift_diagonal_one,
    sub_eq_add_neg, neg_self_module (F := F)]
  change oppositeWedge (F := F) (2,0) +
    (diagonalWedge + ((oppositeWedge (0,0) + diagonalWedge) +
      (oppositeWedge (1,0) + diagonalWedge))) = starMissingDirection
  have hd : diagonalWedge (F := F) + diagonalWedge = 0 := by
    rw [← two_smul F, (CharTwo.two_eq_zero (R := F)), zero_smul]
  calc
    _ = starMissingDirection (F := F) + (diagonalWedge + diagonalWedge) := by
      unfold starMissingDirection
      abel
    _ = _ := by rw [hd, add_zero]

private theorem projection_opposite_mem (r : ShortRootLabel) :
    starProjectionLinear (oppositeWedge (F := F) r) ∈ admissibleWedgeSpan := by
  apply projection_mem_of_add (opposite_difference_mem r (r.1,0) rfl)
  rcases r with ⟨b,j⟩
  fin_cases b
  · change starProjectionLinear (oppositeWedge (F := F) (0,0)) ∈ admissibleWedgeSpan
    rw [projection_opposite_base_zero]
    exact (admissibleWedgeSpan (F := F)).zero_mem
  · change starProjectionLinear (oppositeWedge (F := F) (1,0)) ∈ admissibleWedgeSpan
    rw [projection_opposite_base_one]
    exact (admissibleWedgeSpan (F := F)).zero_mem
  · change starProjectionLinear (oppositeWedge (F := F) (2,0)) ∈ admissibleWedgeSpan
    rw [projection_opposite_base_two]
    exact starMissingDirection_mem_admissibleWedgeSpan

private theorem projection_diagonal_root_mem (i : Fin 3) (r : ShortRootLabel) :
    starProjectionLinear (wedge (diagonalVector (F := F) i) (rootVector r)) ∈
      admissibleWedgeSpan := by
  by_cases h : i = r.1
  · subst i
    have hm := wedge_mem_admissibleWedgeSpan (diagonalRoot_domain (F := F) r)
    rwa [projection_of_mem hm]
  · rw [projection_wedge, diagonalRootPolar, zero_smul, zero_add,
      diagonalRootCross, if_neg h, lift_root, sub_eq_add_neg, neg_self_module (F := F)]
    exact diagonalRoot_difference_mem_admissibleWedgeSpan r i (auxiliaryDiagonal r)
      h (auxiliaryDiagonal_ne r)

private theorem projection_root_root_mem (r s : ShortRootLabel) :
    starProjectionLinear (wedge (rootVector (F := F) r) (rootVector s)) ∈
      admissibleWedgeSpan := by
  by_cases ho : s = (r.1, Fin.rev r.2)
  · subst s
    exact projection_opposite_mem r
  · by_cases hs : ∃ t, scaledShortRoot r + scaledShortRoot s = scaledShortRoot t
    · obtain ⟨t, ht⟩ := hs
      rw [projection_wedge, rootPolar, if_neg ho, zero_smul, zero_add,
        rootCross_shortSum r s t ht, lift_root, sub_eq_add_neg, neg_self_module (F := F)]
      exact rootSum_section_wedge_mem_admissibleWedgeSpan r s t ht
    · have hd : StarDomain (rootVector (F := F) r) (rootVector s) := by
        refine ⟨by rw [rootPolar, if_neg ho], rootCross_noSum r s ho ?_⟩
        simpa only [not_exists] using hs
      have hm := wedge_mem_admissibleWedgeSpan hd
      rwa [projection_of_mem hm]

private theorem projection_diagonal_diagonal_mem (i j : Fin 2) :
    starProjectionLinear (wedge (diagonalVector (F := F) (Fin.castLE (by decide) i))
      (diagonalVector (Fin.castLE (by decide) j))) ∈ admissibleWedgeSpan := by
  have hself (u : TraceZero F) : wedge u u = 0 :=
    (exteriorPower.ιMulti F 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have h01 : starProjectionLinear (wedge (diagonalVector (F := F) 0) (diagonalVector 1)) = 0 := by
    rw [projection_wedge, diagonalPolar, if_neg (by decide), diagonalCross,
      one_smul, _root_.map_zero, add_zero]
    exact sub_self _
  fin_cases i <;> fin_cases j
  · rw [hself, _root_.map_zero]
    exact (admissibleWedgeSpan (F := F)).zero_mem
  · change starProjectionLinear (wedge (diagonalVector (F := F) 0) (diagonalVector 1)) ∈ admissibleWedgeSpan
    rw [h01]
    exact (admissibleWedgeSpan (F := F)).zero_mem
  · change starProjectionLinear (wedge (diagonalVector (F := F) 1) (diagonalVector 0)) ∈ admissibleWedgeSpan
    rw [wedge_comm_charTwo, h01]
    exact (admissibleWedgeSpan (F := F)).zero_mem
  · rw [hself, _root_.map_zero]
    exact (admissibleWedgeSpan (F := F)).zero_mem

/-- Every vector in the joint polar/cross kernel is a linear combination of
wedges from the assigned partial domain, over every characteristic-two ring. -/
theorem admissibleWedgeSpan_eq_starCarrier :
    admissibleWedgeSpan (F := F) = StarCarrier := by
  apply le_antisymm admissibleWedgeSpan_le
  apply starCarrier_le_of_marked_projection
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [markedBasis_diagonal, markedBasis_diagonal]
      exact projection_diagonal_diagonal_mem i j
    | inr r =>
      rw [markedBasis_diagonal, markedBasis_root]
      exact projection_diagonal_root_mem _ r
  | inr r =>
    cases j with
    | inl i =>
      rw [markedBasis_root, markedBasis_diagonal, wedge_comm_charTwo]
      exact projection_diagonal_root_mem _ r
    | inr s =>
      rw [markedBasis_root, markedBasis_root]
      exact projection_root_root_mem r s

end Atlas.ReeF4
