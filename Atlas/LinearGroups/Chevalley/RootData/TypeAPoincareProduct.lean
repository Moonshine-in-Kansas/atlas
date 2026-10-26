import Atlas.LinearGroups.Chevalley.RootData.TypeAPoincareFactor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin

/-! Arithmetic evaluation of the actual type-A Weyl sum in every rank.
The geometric factors are derived from actual parabolic cosets. -/
namespace Atlas.Chevalley.TypeAData
open RootData

theorem rootWeylPoincareEval_A_product_mul (r q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ r * rootWeylPoincareEval (pairing (r + 1)) (base r) q =
      ∏ d ∈ Finset.range r, (q ^ (d + 2) - 1) := by
  induction r with
  | zero => simp [rootWeylPoincareEval_A_zero]
  | succ r ih =>
    have hg : (∑ k : Fin (r + 2), q ^ k.val) * (q - 1) = q ^ (r + 2) - 1 := by
      simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq (r + 2)
    rw [rootWeylPoincareEval_A_succ, pow_succ, Finset.prod_range_succ]
    calc
      _ = ((q - 1) ^ r * rootWeylPoincareEval (pairing (r + 1)) (base r) q) *
          ((∑ k : Fin (r + 2), q ^ k.val) * (q - 1)) := by ac_rfl
      _ = _ := by rw [ih, hg]

end Atlas.Chevalley.TypeAData
