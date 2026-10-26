import Atlas.LinearGroups.Chevalley.RootData.E8PoincareProduct
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin

/-! Geometric-sum arithmetic for the actual E8 Weyl length polynomial. -/
namespace Atlas.Chevalley.E8E7
open RootData

theorem rootWeylPoincareEval_E8_numerator (q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ 8 * rootWeylPoincareEval E8Data.pairing E8Data.base q =
      (q ^ 2 - 1) * (q ^ 8 - 1) * (q ^ 12 - 1) * (q ^ 14 - 1) *
      (q ^ 18 - 1) * (q ^ 20 - 1) * (q ^ 24 - 1) * (q ^ 30 - 1) := by
  have hg (d : ℕ) : (∑ k : Fin d, q ^ k.val) * (q - 1) = q ^ d - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq d
  rw [rootWeylPoincareEval_E8_product]
  calc
    _ = ((∑ k : Fin 2, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 8, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 12, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 14, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 18, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 20, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 24, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 30, q ^ k.val) * (q - 1)) := by ring
    _ = _ := by rw [hg 2, hg 8, hg 12, hg 14, hg 18, hg 20, hg 24, hg 30]

end Atlas.Chevalley.E8E7
