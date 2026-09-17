import Atlas.LinearGroups.Orthogonal.BFamily
import Atlas.LinearGroups.Orthogonal.B1ConjugationComparison
import Atlas.LinearGroups.ProjectiveSpecialLinear

/-! # Independent order of the actual B family in every positive rank -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

def B_good (n q : ℕ) : Prop := 1 ≤ n ∧ 2 ≤ q ∧
  (n, q) ≠ (1, 2) ∧ (n, q) ≠ (1, 3) ∧ (n, q) ≠ (2, 2)

theorem B_card_mul_denominator_all_rank (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (B n F) * B_order_denominator (Nat.card F) = B_order_numerator n (Nat.card F) := by
  by_cases h : n = 1
  · subst n
    rw [Nat.card_congr (B1Conjugation.projectiveEquivPSL (F := F)).toEquiv]
    have ho := Atlas.card_psl_mul_pgl (ι := Fin 2) (F := F)
    rw [Atlas.card_pgl_factor] at ho
    norm_num [Finset.prod_Icc_succ_top] at ho
    simpa [B_order_denominator,B_order_numerator] using ho
  · exact B_card_mul_denominator n (by omega)

theorem B_order_divisibility_all_rank (n : ℕ) (hn : 1 ≤ n) :
    B_order_denominator (Nat.card F) ∣ B_order_numerator n (Nat.card F) :=
  ⟨Nat.card (B n F),(B_card_mul_denominator_all_rank n hn).symm.trans (Nat.mul_comm _ _)⟩

theorem B_card_all_rank (n : ℕ) (hn : 1 ≤ n) : Nat.card (B n F) = B_order n (Nat.card F) := by
  unfold B_order
  rw [← B_card_mul_denominator_all_rank n hn,
    Nat.mul_div_cancel _ (B_order_denominator_positive (Nat.card F))]

end Atlas.Orthogonal
