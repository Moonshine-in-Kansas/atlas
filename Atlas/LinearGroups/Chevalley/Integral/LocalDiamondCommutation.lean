/-
Adapted from mathlib RootSystem/GeckConstruction/Relations.lean.
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in mathlib's LICENSE.
Authors: Oliver Nash; local arithmetic-hypothesis adaptation by ATLAS contributors.
-/
import Atlas.LinearGroups.Chevalley.OppositeSimpleCommutation

/-! Local arithmetic repair: concrete diamond
providers are still required for every actual root datum. No irreducibility
instance over ℤ or IsNotG2 instance is assumed or manufactured. -/
noncomputable section
namespace Atlas.Chevalley.Integral

/-- The product identity around a genuine simple-root diamond.
This is a root-string arithmetic property, not a matrix/group commutation claim. -/
def SimpleDiamondProducts {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Finite ι] [IsDomain R] [CharZero R]
    (P : RootPairing ι R M N) [P.IsCrystallographic] (b : P.Base) : Prop :=
  ∀ (i j : b.support), i ≠ j → ∀ k l m : ι,
    P.root k + P.root i = P.root l →
    P.root k - P.root j = P.root m →
    P.root k + P.root i - P.root j ∈ Set.range P.root →
    (P.chainBotCoeff i m + 1) * (P.chainTopCoeff j k + 1) =
      (P.chainTopCoeff j l + 1) * (P.chainBotCoeff i k + 1)

end Atlas.Chevalley.Integral
namespace RootPairing.GeckConstruction.LocalDiamond
open Function Module.End
open Set hiding diagonal
variable {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base} [Fintype ι]
  (i j : b.support)
attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply
variable [P.IsReduced]

open scoped Matrix

variable {i j}
variable (hij : i ≠ j)
omit [P.IsReduced]

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₀ (k : b.support) (l : ι) :
    ⁅e i, f j⁆ (Sum.inl k) (Sum.inr l) = 0 := by
  classical
  let := P.indexNeg
  have aux₁ : ∀ x ∈ Finset.univ, ¬ (P.root x = P.root i + P.root l ∧ k = j ∧ x = j) := by
    rintro x - ⟨hl, -, rfl⟩
    exact b.sub_notMem_range_root i.property j.property ⟨-l, by simp [hl]⟩
  have aux₂ : ∀ x ∈ Finset.univ, ¬ (P.root x = P.root l - P.root j ∧ k = i ∧ x = -i) := by
    rintro x - ⟨hl, -, rfl⟩
    replace hl : P.root i = P.root j - P.root l := by simpa [neg_eq_iff_eq_neg] using hl
    exact b.sub_notMem_range_root i.property j.property ⟨-l, by simp [hl]⟩
  simp [e, f, -indexNeg_neg, ← ite_and, Finset.sum_ite_of_false aux₁, Finset.sum_ite_of_false aux₂]

include hij

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₁ :
    ⁅e i, f j⁆ᵀ (Sum.inr j) = 0 := by
  have hij' : (i : ι) ≠ (j : ι) := hij ∘ SetLike.coe_eq_coe.mp
  let := P.indexNeg
  classical
  ext (k | k)
  · rw [Matrix.transpose_apply, lie_e_f_ne_aux₀, Pi.zero_apply]
  · suffices ((if k = i then ↑|b.cartanMatrix i j| else (0 : R)) -
        ∑ x, if P.root x = P.root i + P.root j ∧ P.root k = P.root x - P.root j then
          (P.chainTopCoeff j x : R) + 1 else 0) = 0 by
      have hij : (j : ι) ≠ -i := by simpa using b.root_ne_neg_of_ne j.property i.property hij'.symm
      have aux : ∀ x ∈ Finset.univ,
        x ≠ j → (if x = j ∧ k = i then ↑|b.cartanMatrix i x| else 0) = (0 : R) := by aesop
      simpa [e, f, P.ne_zero, hij, -indexNeg_neg, -Finset.univ_eq_attach, ← ite_and,
        Finset.sum_eq_single_of_mem j (Finset.mem_univ _) aux]
    rcases eq_or_ne k i with rfl | hk; swap
    · rw [ite_eq_right (by tauto), Finset.sum_ite_of_false (by aesop)]; simp
    by_cases hij_mem : P.root i + P.root j ∈ range P.root
    · obtain ⟨m, hm⟩ := hij_mem
      rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _) (by rintro x - hx; simp [← hm, hx]),
        b.abs_cartanMatrix_apply, Base.cartanMatrix, Base.cartanMatrixIn_def]
      have aux₁ := b.chainTopCoeff_eq_of_ne hij.symm
      have aux₂ := chainTopCoeff_of_add (b.linearIndependent_pair_of_ne hij.symm) hm
      norm_cast
      aesop
    · have aux : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root j ∧ P.root i = P.root x - P.root j) := by
        rintro x - ⟨hx, -⟩; exact hij_mem ⟨x, hx⟩
      simp [Finset.sum_ite_of_false aux, b.cartanMatrix_apply_eq_zero_iff hij, hij_mem]

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₂ :
    letI := P.indexNeg
    ⁅e i, f j⁆ᵀ (Sum.inr (-i)) = 0 := by
  let := P.indexNeg
  classical
  ext (k | k)
  · rw [Matrix.transpose_apply, lie_e_f_ne_aux₀, Pi.zero_apply]
  · have aux : ⁅e i, f j⁆ (.inr k) (.inr (-i)) = (⁅e i, f j⁆ * ω b) (.inr k) (.inr i) := by simp [ω]
    rw [Matrix.transpose_apply, aux, lie_e_f_mul_ω, ← (-ω b * ⁅e j, f i⁆).transpose_apply,
      Matrix.transpose_mul, Matrix.mul_apply', lie_e_f_ne_aux₁ hij.symm]
    simp

/-- Lemma 3.5 from [Geck](Geck2017). -/
lemma lie_e_f_ne_of_local_diamond [P.IsReduced]
    (hdiamond : Atlas.Chevalley.Integral.SimpleDiamondProducts P b) :
    ⁅e i, f j⁆ = 0 := by
  have hij' : (i : ι) ≠ (j : ι) := hij ∘ SetLike.coe_eq_coe.mp
  let := P.indexNeg
  classical
  ext (k | k) (l | l)
  · rw [ne_comm] at hij
    simp_all [-indexNeg_neg, e, f]
  · exact lie_e_f_ne_aux₀ k l
  · have aux₁ : P.root k ≠ P.root i - P.root j :=
      fun contra ↦ b.sub_notMem_range_root i.property j.property ⟨k, contra⟩
    simp [e, f, ← sub_eq_add_neg, ite_eq_right aux₁]
  · /- Geck Case 1 (covered by the auxiliary lemmas above). -/
    rcases eq_or_ne l j with rfl | h₃
    · rw [← ⁅e i, f j⁆.transpose_apply, lie_e_f_ne_aux₁ hij, Pi.zero_apply, Matrix.zero_apply]
    rcases eq_or_ne l (-i) with rfl | h₄
    · rw [← ⁅e i, f j⁆.transpose_apply, lie_e_f_ne_aux₂ hij, Pi.zero_apply, Matrix.zero_apply]
    /- Geck Case 2.
    It's all just definition unfolding and case analysis: the only real content is the external
    lemma `chainBotCoeff_mul_chainTopCoeff`. -/
    suffices
      (∑ x, if P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x then
          ((P.chainBotCoeff i x : R) + 1) * (P.chainTopCoeff j l + 1) else 0) =
      (∑ x, if P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j then
          ((P.chainTopCoeff j x : R) + 1) * (P.chainBotCoeff i l + 1) else 0) by
      have h₁ : ∀ x ∈ Finset.univ, ¬ ((x = i ∧ l = -i) ∧ k = -j) := by
        rintro - - ⟨⟨-, contra⟩, -⟩; contradiction
      have h₂ : ∀ x ∈ Finset.univ, ¬ ((x = j ∧ l = j) ∧ k = i) := by
        rintro - - ⟨⟨-, contra⟩, -⟩; contradiction
      rw [← sub_eq_zero] at this
      simpa [e, f, ← ite_and, Finset.sum_ite_of_false h₁, Finset.sum_ite_of_false h₂, -indexNeg_neg,
        -Finset.univ_eq_attach]
    by_cases h₅ : P.root l + P.root i - P.root j ∈ range P.root; swap
    · have aux₃ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        rintro x - ⟨hx, hx'⟩; exact h₅ ⟨k, by rw [hx', hx]; abel⟩
      have aux₄ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        rintro x - ⟨hx, hx'⟩; exact h₅ ⟨k, by rw [hx', hx]; abel⟩
      simp [Finset.sum_ite_of_false aux₃, Finset.sum_ite_of_false aux₄]
    by_cases h₆ : P.root l + P.root i ∈ range P.root; swap
    · have h₇ : P.root l - P.root j ∉ range P.root := by
        rwa [b.root_sub_mem_iff_root_add_mem i j l hij' i.property j.property h₃ _ h₅]
        simpa
      have aux₃ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        rintro x - ⟨hx, -⟩; exact h₆ ⟨x, by rw [hx]; abel⟩
      have aux₄ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        rintro x - ⟨hx, hx'⟩; exact h₇ ⟨x, hx⟩
      simp [Finset.sum_ite_of_false aux₃, Finset.sum_ite_of_false aux₄]
    obtain ⟨m, hm : P.root m = P.root l - P.root j⟩ :=
      b.root_sub_root_mem_of_mem_of_mem i j l hij' i.property j.property h₅ h₃ h₆
    obtain ⟨l', hl'⟩ := h₆
    by_cases hk : P.root k = P.root l + P.root i - P.root j; swap
    · grind
    have aux₃ (x) (hx : x ≠ m) :
      ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        grind [EmbeddingLike.apply_eq_iff_eq]
    have aux₄ (x) (hx : x ≠ l') :
      ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        grind [EmbeddingLike.apply_eq_iff_eq]
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _) (by
        rintro x - h
        rw [ite_eq_right (aux₃ _ h)]),
      Finset.sum_eq_single_of_mem l' (Finset.mem_univ _) (by
        rintro x - h
        rw [ite_eq_right (aux₄ _ h)]),
      ite_eq_left (⟨hm, by rw [hm, hk]; abel⟩),
      ite_eq_left ⟨by rw [hl', add_comm], by rw [hl', hk]⟩]
    have := hdiamond i j hij l l' m hl'.symm hm.symm h₅
    norm_cast


end RootPairing.GeckConstruction.LocalDiamond

namespace Atlas.Chevalley.Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : Integral.SimpleDiamondProducts P b)

include hdiamond

omit [DecidableEq ι] in
/-- The genuine Geck raising and opposite lowering operators commute when the
simple indices are distinct. -/
theorem raising_lowering_commute_of_diamond (i j : b.support) (hij : i ≠ j) :
    Commute (raising P b i) (lowering P b j) := by
  have h := RootPairing.GeckConstruction.LocalDiamond.lie_e_f_ne_of_local_diamond (b := b) hij hdiamond
  simpa only [Commute, SemiconjBy, Ring.lie_def, sub_eq_zero] using h

theorem raising_lowering_divided_commute_of_diamond (i j : b.support) (hij : i ≠ j) (k l : ℕ) :
    Commute (raisingDividedPower P b i k) (loweringDividedPower P b j l) :=
  divided_matrices_commute (raising P b i) (lowering P b j) _ _ k l
    (raising_lowering_commute_of_diamond P b hdiamond i j hij)
    (factorial_smul_raisingDividedPower P b i k)
    (factorial_smul_loweringDividedPower P b j l)

variable (R : Type*) [CommRing R]

theorem raising_lowering_dividedOver_commute_of_diamond (i j : b.support) (hij : i ≠ j) (k l : ℕ) :
    Commute (raisingDividedOver P b R i k)
      ((loweringDividedPower P b j l).map (Int.castRingHom R)) := by
  have h := congrArg (fun A => A.map (Int.castRingHom R))
    (raising_lowering_divided_commute_of_diamond P b hdiamond i j hij k l).eq
  simpa only [Commute, SemiconjBy, Matrix.map_mul, raisingDividedOver] using h

/-- Every commutative coefficient ring is allowed, including characteristics
2 and 3; no factorial is cancelled in this ring. -/
theorem raising_lowering_exponential_commute_of_diamond (i j : b.support) (hij : i ≠ j) (s t : R) :
    Commute (raisingExponential P b R i s) (loweringExponential P b R j t) := by
  unfold raisingExponential loweringExponential
  apply Commute.sum_left
  intro k hk
  apply Commute.sum_right
  intro l hl
  exact ((raising_lowering_dividedOver_commute_of_diamond P b hdiamond R i j hij k l).smul_left (s^k)).smul_right (t^l)

end Atlas.Chevalley.Integral
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : Integral.SimpleDiamondProducts P b) (R : Type*) [CommRing R]

include hdiamond

/-- Opposite root elements in the actual generated adjoint group commute for
distinct simple indices. -/
theorem adjointX_commute_adjointY_of_diamond (i j : b.support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX P b R i s) (adjointY P b R j t) := by
  change adjointX P b R i s * adjointY P b R j t =
    adjointY P b R j t * adjointX P b R i s
  apply Subtype.ext
  apply Units.ext
  change raisingExponential P b R i s * (loweringRootElement P b R j t).val =
    (loweringRootElement P b R j t).val * raisingExponential P b R i s
  rw [loweringRootElement_val]
  exact (raising_lowering_exponential_commute_of_diamond P b hdiamond R i j hij s t).eq

end Atlas.Chevalley
