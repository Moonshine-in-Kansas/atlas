import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic.NormNum

/-! UNCOMPILED source candidate. Finite conjugation on a length-four
operator string over a rational algebra. No target group is assumed. -/

noncomputable section
namespace Atlas.Algebra

variable {S : Type*} [Ring S] [Algebra ℚ S]

private theorem exp_mulLeft_apply (A B : S) (hA : IsNilpotent A) :
    IsNilpotent.exp (LinearMap.mulLeft ℚ A) B = IsNilpotent.exp A * B := by
  obtain ⟨N, hN⟩ := hA
  have hL : (LinearMap.mulLeft ℚ A) ^ N = 0 := by
    rw [LinearMap.pow_mulLeft]
    ext x
    simp only [LinearMap.mulLeft_apply, hN, zero_mul, LinearMap.zero_apply]
  rw [IsNilpotent.exp_eq_sum hL, IsNilpotent.exp_eq_sum hN]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.pow_mulLeft,
    LinearMap.mulLeft_apply, Finset.sum_mul, smul_mul_assoc]

private theorem exp_mulRight_apply (A B : S) (hA : IsNilpotent A) :
    IsNilpotent.exp (LinearMap.mulRight ℚ A) B = B * IsNilpotent.exp A := by
  obtain ⟨N, hN⟩ := hA
  have hR : (LinearMap.mulRight ℚ A) ^ N = 0 := by
    rw [LinearMap.pow_mulRight]
    ext x
    simp only [LinearMap.mulRight_apply, hN, mul_zero, LinearMap.zero_apply]
  rw [IsNilpotent.exp_eq_sum hR, IsNilpotent.exp_eq_sum hN]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.pow_mulRight,
    LinearMap.mulRight_apply, Finset.mul_sum, mul_smul_comm]

/-- The degree-three finite Hadamard formula. Only the conjugating operator
is assumed nilpotent; C=[A,B], D=[A,C], E=[A,D], and [A,E]=0 are explicit. -/
theorem exp_mul_mul_exp_neg_eq_add_add_half_add_sixth
    (A B C D E : S) (hA : IsNilpotent A)
    (hAB : A * B - B * A = C) (hAC : A * C - C * A = D)
    (hAD : A * D - D * A = E) (hAE : Commute A E) :
    IsNilpotent.exp A * B * IsNilpotent.exp (-A) =
      B + C + (1 / 2 : ℚ) • D + (1 / 6 : ℚ) • E := by
  let δ : Module.End ℚ S := LinearMap.mulLeft ℚ A + LinearMap.mulRight ℚ (-A)
  have hδ (x : S) : δ x = A * x - x * A := by
    simp only [δ, LinearMap.add_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, mul_neg, sub_eq_add_neg]
  have hL : IsNilpotent (LinearMap.mulLeft ℚ A) :=
    (LinearMap.isNilpotent_mulLeft_iff ℚ A).mpr hA
  have hR : IsNilpotent (LinearMap.mulRight ℚ (-A)) :=
    (LinearMap.isNilpotent_mulRight_iff ℚ (-A)).mpr hA.neg
  have hcomm : Commute (LinearMap.mulLeft ℚ A) (LinearMap.mulRight ℚ (-A)) :=
    LinearMap.commute_mulLeft_right A (-A)
  have hnil : IsNilpotent δ := hcomm.isNilpotent_add hL hR
  have hfourth : (δ ^ 4) B = 0 := by
    simp only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply,
      hδ, hAB, hAC, hAD, sub_eq_zero.mpr hAE.eq]
  have htrunc := IsNilpotent.exp_smul_eq_sum (M := S) (a := δ) (m := B)
    (k := 4) hfourth hnil
  change IsNilpotent.exp δ B =
    ∑ k ∈ Finset.range 4, ((k.factorial : ℚ)⁻¹ • δ ^ k) B at htrunc
  have hvalue : IsNilpotent.exp δ B = B + C + (1 / 2 : ℚ) • D + (1 / 6 : ℚ) • E := by
    simpa [Finset.sum_range_succ, pow_succ, Module.End.mul_apply,
      hδ, hAB, hAC, hAD, show Nat.factorial 3 = 6 from rfl] using htrunc
  have hexp : IsNilpotent.exp δ =
      IsNilpotent.exp (LinearMap.mulLeft ℚ A) *
        IsNilpotent.exp (LinearMap.mulRight ℚ (-A)) :=
    IsNilpotent.exp_add_of_commute hcomm hL hR
  rw [hexp, Module.End.mul_apply, exp_mulRight_apply (-A) B hA.neg,
    exp_mulLeft_apply A (B * IsNilpotent.exp (-A)) hA] at hvalue
  simpa only [mul_assoc] using hvalue

end Atlas.Algebra
