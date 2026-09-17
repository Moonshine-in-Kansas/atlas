import Atlas.LinearGroups.Orthogonal.D2MatrixComparison
import Atlas.LinearGroups.ProjectiveSpecialLinear

/-! # Order of the actual low-rank split-D product model

This is a consequence of the actual PSL2-product comparison and the independent
PSL order formula. No simplicity or perfectness of SL2 is used, including at q=2,3.
-/
noncomputable section
namespace Atlas.Orthogonal.D2Matrix
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]

/-- Actual D2 order as the square of the actual PSL2 order. -/
theorem card_projectiveD_two_eq_psl_square :
    Nat.card (ProjectiveElementary (formD 2 F)) = Nat.card (PSL(2,F)) ^ 2 := by
  rw [Nat.card_congr (projectiveEquivProduct (F := F)).toEquiv,Nat.card_prod,pow_two]

/-- The exact multiplied formula retains the full scalar denominator. -/
theorem card_projectiveD_two_mul_gcd_square :
    Nat.card (ProjectiveElementary (formD 2 F)) * Nat.gcd 2 (Nat.card F - 1) ^ 2 =
      Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
  have h := Atlas.card_psl_mul_pgl (ι := Fin 2) (F := F)
  rw [Atlas.card_pgl_factor] at h
  norm_num [Finset.prod_Icc_succ_top] at h
  rw [card_projectiveD_two_eq_psl_square]
  calc
    Nat.card (PSL(2,F)) ^ 2 * Nat.gcd 2 (Nat.card F - 1) ^ 2 =
        (Nat.card (PSL(2,F)) * Nat.gcd 2 (Nat.card F - 1)) ^ 2 := (mul_pow _ _ _).symm
    _ = _ := by rw [h,mul_pow]

/-- Divisibility is a consequence of the actual multiplied order identity. -/
theorem projectiveD_two_order_divisibility :
    Nat.gcd 2 (Nat.card F - 1) ^ 2 ∣ Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
  refine ⟨Nat.card (ProjectiveElementary (formD 2 F)), ?_⟩
  exact card_projectiveD_two_mul_gcd_square.symm.trans (Nat.mul_comm _ _)

/-- Uniform numerical order of the actual projective split-D2 group. -/
theorem card_projectiveD_two :
    Nat.card (ProjectiveElementary (formD 2 F)) =
      (Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2) / Nat.gcd 2 (Nat.card F - 1) ^ 2 := by
  rw [← card_projectiveD_two_mul_gcd_square,
    Nat.mul_div_cancel _ (pow_pos (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 2)) _)]

end Atlas.Orthogonal.D2Matrix
