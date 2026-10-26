import Atlas.LinearGroups.Chevalley.RootData.F4PoincareProduct
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin

/-! Arithmetic evaluation of the actual F4 root-Weyl polynomial. The four
geometric factors are those derived from the actual B3 parabolic, rather
than supplied fundamental degrees or an older F4 order theorem. -/
namespace Atlas.Chevalley.F4B3
open RootData

theorem rootWeylPoincareEval_F4_numerator (q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ 4 * rootWeylPoincareEval F4Data.pairing F4Data.base q =
      (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) * (q ^ 12 - 1) := by
  have hg (d : ℕ) : (∑ k : Fin d, q ^ k.val) * (q - 1) = q ^ d - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq d
  rw [rootWeylPoincareEval_F4_product]
  calc
    _ = ((∑ k : Fin 2, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 6, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 8, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 12, q ^ k.val) * (q - 1)) := by ring
    _ = _ := by rw [hg 2, hg 6, hg 8, hg 12]

end Atlas.Chevalley.F4B3
