import Atlas.LinearGroups.Chevalley.RootData.G2PoincareFactor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin

/-! Arithmetic evaluation of the actual G2 Weyl sum. The only arithmetic
input is mathlib's geometric-sum identity over the naturals. -/
namespace Atlas.Chevalley.G2Parabolic
open RootData

theorem rootWeylPoincareEval_g2_product (q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ 2 * rootWeylPoincareEval G2Data.pairing G2Data.base q =
      (q ^ 6 - 1) * (q ^ 2 - 1) := by
  have h2 : (∑ k : Fin 2, q ^ k.val) * (q - 1) = q ^ 2 - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq 2
  have h6 : (∑ k : Fin 6, q ^ k.val) * (q - 1) = q ^ 6 - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq 6
  rw [rootWeylPoincareEval_g2]
  calc
    _ = ((∑ k : Fin 6, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 2, q ^ k.val) * (q - 1)) := by
      rw [pow_two]
      ac_rfl
    _ = _ := by rw [h6, h2]

end Atlas.Chevalley.G2Parabolic
