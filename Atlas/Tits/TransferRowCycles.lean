import Atlas.Tits.TransferRowCentralizer
import Mathlib.GroupTheory.GroupAction.Period

/-! The restriction of the actual transfer witness to each coordinate row.
Every external row consists of two actual two-cycles. -/

namespace Atlas.Tits
open Atlas.Rudvalis

abbrev CoordinateRowNeighbours (p : Point) :=
  {c : Neighbours // c.val ∈ coordinateRowFrame p}

-- Unfolding the inherited quotient action crosses several nested stabilizers.
set_option maxRecDepth 16384 in
theorem localAlpha_row_mem (p : Point) (c : Neighbours)
    (hc : c.val ∈ coordinateRowFrame p) :
    (localAlpha • c).val ∈ coordinateRowFrame p := by
  obtain ⟨x,hx⟩ := hc
  change localCodeAlpha • c.val ∈ coordinateRowFrame p
  rw [← hx,coordinateCross_action]
  have he := congrArg (fun g : binaryPermutationGroup => g.val (p,x)) localCodeAlpha_translation
  change localCodeAlpha.val.right (p,x) = coordinateTranslation alphaTranslationMatrix (p,x) at he
  rw [he]
  exact ⟨x+matrixAt alphaTranslationMatrix p.val,rfl⟩

/-- This is precisely the restriction of alpha, not an independent row model. -/
noncomputable def alphaRowPerm (p : Point) : Equiv.Perm (CoordinateRowNeighbours p) :=
  Equiv.ofBijective (fun c => ⟨localAlpha • c.val,localAlpha_row_mem p c.val c.prop⟩) (by
    have hi : Function.Injective
        (fun c : CoordinateRowNeighbours p =>
          (⟨localAlpha • c.val,localAlpha_row_mem p c.val c.prop⟩ : CoordinateRowNeighbours p)) := by
      intro c d h
      apply Subtype.ext
      exact (MulAction.injective localAlpha) (congrArg Subtype.val h)
    exact ⟨hi,Finite.surjective_of_injective hi⟩)

theorem alphaRowPerm_apply (p : Point) (c : CoordinateRowNeighbours p) :
    (alphaRowPerm p c).val = localAlpha • c.val := rfl

theorem alphaRowPerm_square (p : Point) : (alphaRowPerm p)^2 = 1 := by
  apply Equiv.ext
  intro c
  apply Subtype.ext
  change localAlpha • (localAlpha • c.val) = c.val
  rw [← mul_smul,← pow_two]
  exact (localAlpha_square_fixed_iff c.val).mpr (coordinateRowFrame_subset p c.prop)

theorem alphaRowPerm_no_fixed (p : Point) (hp : p ≠ rowLabel 0)
    (c : CoordinateRowNeighbours p) : alphaRowPerm p c ≠ c := by
  intro h
  have he : localAlpha • c.val = c.val := congrArg Subtype.val h
  obtain ⟨x,hx⟩ := c.prop
  obtain ⟨y,hy⟩ := (localAlpha_fixed_iff c.val).mp he
  exact hp (coordinateCross_row_of_eq (hx.trans hy.symm))

noncomputable def coordinateRowNeighboursEquiv (p : Point) (hp : p ≠ rowLabel 0) :
    CoordinateRowNeighbours p ≃ coordinateRowFrame p where
  toFun c := ⟨c.val.val,c.prop⟩
  invFun c := ⟨⟨c.val,by
    obtain ⟨x,hx⟩ := c.prop
    rw [← hx,localReferenceCross_eq]
    apply (coordinateFrame_orthogonal_iff _ _ (coordinateCross_mem _) (coordinateCross_mem _)).mpr
    intro he
    exact hp (coordinateCross_row_of_eq he).symm⟩,c.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coordinateRowNeighbours_card (p : Point) (hp : p ≠ rowLabel 0) :
    Nat.card (CoordinateRowNeighbours p) = 4 := by
  rw [Nat.card_congr (coordinateRowNeighboursEquiv p hp),coordinateRowFrame_card]

theorem alphaRowPerm_period_two (p : Point) (hp : p ≠ rowLabel 0)
    (c : CoordinateRowNeighbours p) :
    Function.minimalPeriod (alphaRowPerm p • ·) c = 2 := by
  have hd : Function.minimalPeriod (alphaRowPerm p • ·) c ∣ 2 :=
    MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mp (by rw [alphaRowPerm_square,one_smul])
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
  · have hf : alphaRowPerm p • c = c := MulAction.period_eq_one_iff.mp h
    exact False.elim (alphaRowPerm_no_fixed p hp c hf)
  · exact h

/-- The two-cycle count concerns the literal restriction of alpha to this row. -/
theorem alphaRowPerm_two_cycles_card (p : Point) (hp : p ≠ rowLabel 0) :
    Nat.card (Atlas.GroupTheory.CyclesOfLength (alphaRowPerm p) (CoordinateRowNeighbours p) 2) = 2 := by
  have hpoints : Nat.card {c : CoordinateRowNeighbours p //
      Function.minimalPeriod (alphaRowPerm p • ·) c = 2} = 4 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (alphaRowPerm_period_two p hp))]
    exact coordinateRowNeighbours_card p hp
  have hc := Atlas.GroupTheory.card_period_points (X := CoordinateRowNeighbours p) (alphaRowPerm p) 2
  rw [hpoints] at hc
  omega

end Atlas.Tits
