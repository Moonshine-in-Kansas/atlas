import Atlas.LinearGroups.Chevalley.RootData.ClassicalBCPoincareProduct
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin

/-! Arithmetic evaluation of the B/C Poincaré product. This is a root-data
statement; it assumes no order or simplicity of a constructed group. -/
namespace Atlas.Chevalley.ClassicalBParabolic
open Classical ClassicalData RootData

theorem rootWeylPoincareEval_B_product_mul (n q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ (n + 1) * rootWeylPoincareEval (pairingB (n + 1)) (baseB n) q =
      ∏ d ∈ Finset.range (n + 1), (q ^ (2 * (d + 1)) - 1) := by
  induction n with
  | zero =>
    have hg : (∑ k : Fin 2, q ^ k.val) * (q - 1) = q ^ 2 - 1 := by
      simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq 2
    change (q - 1) ^ 1 * rootWeylPoincareEval (pairingB 1) (baseB 0) q =
      ∏ d ∈ Finset.range 1, (q ^ (2 * (d + 1)) - 1)
    rw [pow_one, rootWeylPoincareEval_B_one, Finset.prod_range_one]
    change (q - 1) * (∑ k : Fin 2, q ^ k.val) = q ^ 2 - 1
    rw [mul_comm]
    exact hg
  | succ n ih =>
    have hg : (∑ k : Fin (2 * (n + 2)), q ^ k.val) * (q - 1) = q ^ (2 * (n + 2)) - 1 := by
      simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq (2 * (n + 2))
    rw [rootWeylPoincareEval_B_succ, pow_succ, Finset.prod_range_succ]
    calc
      _ = ((q - 1) ^ (n + 1) * rootWeylPoincareEval (pairingB (n + 1)) (baseB n) q) *
          ((∑ k : Fin (2 * (n + 2)), q ^ k.val) * (q - 1)) := by ac_rfl
      _ = _ := by rw [ih, hg]

theorem rootWeylPoincareEval_C_product_mul (n q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ (n + 1) * rootWeylPoincareEval (pairingC (n + 1)) (baseC n) q =
      ∏ d ∈ Finset.range (n + 1), (q ^ (2 * (d + 1)) - 1) := by
  rw [← rootWeylPoincareEval_B_eq_C]
  exact rootWeylPoincareEval_B_product_mul n q hq

end Atlas.Chevalley.ClassicalBParabolic
