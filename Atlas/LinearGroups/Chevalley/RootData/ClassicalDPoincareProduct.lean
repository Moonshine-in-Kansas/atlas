import Atlas.LinearGroups.Chevalley.RootData.ClassicalDPoincareRecurrence
import Atlas.LinearGroups.Chevalley.RootData.ClassicalDRankTwoPoincare
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin

/-! Uniform degree product for the actual D Weyl image. The extra degree r
is retained separately from 2,4,...,2r−2, including its even-rank repetition. -/
namespace Atlas.Chevalley.ClassicalDParabolic
open Classical ClassicalData RootData

private theorem geom_sum_double (m q : ℕ) :
    (∑ k : Fin (2 * m), q ^ k.val) =
      (∑ k : Fin m, q ^ k.val) * (1 + q ^ m) := by
  simp only [Fin.sum_univ_eq_sum_range]
  rw [two_mul, Finset.sum_range_add]
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  ring

/-- Actual type-D length sum, uniformly from the D₂ base and the proved
right-parabolic recurrence. No division by a geometric factor is used. -/
theorem rootWeylPoincareEval_D_product (n q : ℕ) :
    rootWeylPoincareEval (pairingD (n + 2)) (baseD n) q =
      (∑ k : Fin (n + 2), q ^ k.val) *
        ∏ d ∈ Finset.range (n + 1), (∑ k : Fin (2 * (d + 1)), q ^ k.val) := by
  induction n with
  | zero =>
    rw [rootWeylPoincareEval_D_two, Finset.prod_range_one]
    change (1 + q) ^ 2 = (∑ k : Fin 2, q ^ k.val) * (∑ k : Fin 2, q ^ k.val)
    simp [Fin.sum_univ_two, pow_two]
  | succ n ih =>
    conv_rhs => rw [Finset.prod_range_succ]
    rw [rootWeylPoincareEval_D_succ, ih]
    calc
      _ = (∑ k : Fin (n + 3), q ^ k.val) *
          ((∏ d ∈ Finset.range (n + 1), (∑ k : Fin (2 * (d + 1)), q ^ k.val)) *
            ((∑ k : Fin (n + 2), q ^ k.val) * (1 + q ^ (n + 2)))) := by ac_rfl
      _ = _ := by rw [← geom_sum_double]

end Atlas.Chevalley.ClassicalDParabolic
