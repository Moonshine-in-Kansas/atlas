import Atlas.LinearGroups.Chevalley.RootData.E7PoincareProduct

/-! The degree numerator of the actual E7 root-Weyl polynomial. -/
namespace Atlas.Chevalley.E7E6
open RootData

theorem rootWeylPoincareEval_E7_numerator (q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ 7 * rootWeylPoincareEval E7Data.pairing E7Data.base q =
      (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) * (q ^ 10 - 1) *
      (q ^ 12 - 1) * (q ^ 14 - 1) * (q ^ 18 - 1) := by
  have hg (d : ℕ) : (∑ k : Fin d, q ^ k.val) * (q - 1) = q ^ d - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq d
  rw [rootWeylPoincareEval_E7_product]
  calc
    _ = ((∑ k : Fin 2, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 6, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 8, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 10, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 12, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 14, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 18, q ^ k.val) * (q - 1)) := by ring
    _ = _ := by rw [hg 2, hg 6, hg 8, hg 10, hg 12, hg 14, hg 18]

end Atlas.Chevalley.E7E6
