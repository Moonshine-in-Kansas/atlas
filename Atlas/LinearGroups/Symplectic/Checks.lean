import Atlas.LinearGroups.TypeC

namespace Atlas.Symplectic.Checks
variable {F : Type*} [Field F] [Finite F]

/-- All numerical checks below specialize the uniform theorems; no matrix enumeration. -/
theorem rank_zero : Nat.card (Sp 0 F)=1 ∧ Nat.card (PSp 0 F)=1 ∧
    ¬ IsSimpleGroup (PSp 0 F) :=
  ⟨card_rank_zero,card_projective_rank_zero,rank_zero_not_simple⟩

theorem rank1_card2 (hq : Nat.card F=2) :
    Nat.card (Sp 1 F)=6 ∧ Nat.card (PSp 1 F)=6 ∧
    ¬ IsSimpleGroup (PSp 1 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank1_card3 (hq : Nat.card F=3) :
    Nat.card (Sp 1 F)=24 ∧ Nat.card (PSp 1 F)=12 ∧
    ¬ IsSimpleGroup (PSp 1 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank1_card4 (hq : Nat.card F=4) :
    Nat.card (Sp 1 F)=60 ∧ Nat.card (PSp 1 F)=60 ∧
    IsSimpleGroup (PSp 1 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank2_card2 (hq : Nat.card F=2) :
    Nat.card (Sp 2 F)=720 ∧ Nat.card (PSp 2 F)=720 ∧
    ¬ IsSimpleGroup (PSp 2 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank2_card3 (hq : Nat.card F=3) :
    Nat.card (Sp 2 F)=51840 ∧ Nat.card (PSp 2 F)=25920 ∧
    IsSimpleGroup (PSp 2 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank2_card4 (hq : Nat.card F=4) :
    Nat.card (Sp 2 F)=979200 ∧ Nat.card (PSp 2 F)=979200 ∧
    IsSimpleGroup (PSp 2 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank2_card5 (hq : Nat.card F=5) :
    Nat.card (Sp 2 F)=9360000 ∧ Nat.card (PSp 2 F)=4680000 ∧
    IsSimpleGroup (PSp 2 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank3_card2 (hq : Nat.card F=2) :
    Nat.card (Sp 3 F)=1451520 ∧ Nat.card (PSp 3 F)=1451520 ∧
    IsSimpleGroup (PSp 3 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank3_card3 (hq : Nat.card F=3) :
    Nat.card (Sp 3 F)=9170703360 ∧ Nat.card (PSp 3 F)=4585351680 ∧
    IsSimpleGroup (PSp 3 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

theorem rank4_card2 (hq : Nat.card F=2) :
    Nat.card (Sp 4 F)=47377612800 ∧ Nat.card (PSp 4 F)=47377612800 ∧
    IsSimpleGroup (PSp 4 F) := by
  rw [card_sp,card_psp (by decide),simple_iff_good,hq]
  norm_num [orderNumerator,Finset.prod_range_succ,Good]

/-- Order four means the actual degree-two Galois field, never ZMod 4. -/
theorem galois_four : Nat.card (Sp 2 (GaloisField 2 2))=979200 ∧
    Nat.card (PSp 2 (GaloisField 2 2))=979200 ∧
    IsSimpleGroup (PSp 2 (GaloisField 2 2)) := by
  apply rank2_card4
  simpa using GaloisField.card 2 2 (by decide)

theorem small_perfectness : Group.IsPerfect (Sp 2 (ZMod 3)) ∧
    Group.IsPerfect (Sp 3 (ZMod 2)) := by
  constructor
  · apply perfect_of_card_three (by decide)
    simp [Nat.card_eq_fintype_card]
  · apply perfect_of_card_two (by decide)
    simp [Nat.card_eq_fintype_card]

/-- The other ten refinements have ten zeros; this checks only 16 by 16 scalar data. -/
theorem binary_zero_counts (a : BinaryException.V) :
    BinaryException.zeroCount (BinaryException.refinementOf a) =
      if BinaryException.baseQuadratic a=1 then 6 else 10 := by
  unfold BinaryException.zeroCount
  rw [Nat.card_eq_fintype_card]
  exact (by decide +kernel : ∀ a : BinaryException.V,
    Fintype.card {x : BinaryException.V // (BinaryException.refinementOf a).val x=0} =
      if BinaryException.baseQuadratic a=1 then 6 else 10) a

end Atlas.Symplectic.Checks

