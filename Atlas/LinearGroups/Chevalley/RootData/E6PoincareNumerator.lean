import Atlas.LinearGroups.Chevalley.RootData.E6PoincareProduct

/-! The degree numerator of the actual E6 root-Weyl polynomial. -/
noncomputable section
namespace Atlas.Chevalley.E6D5
open Classical RootData
local instance : Fintype E6Data.Root := Fintype.ofFinite _

theorem rootWeylPoincareEval_E6_numerator (q : ℕ) (hq : 1 ≤ q) :
    (q - 1) ^ 6 * rootWeylPoincareEval E6Data.pairing E6Data.base q =
      (q ^ 2 - 1) * (q ^ 5 - 1) * (q ^ 6 - 1) *
      (q ^ 8 - 1) * (q ^ 9 - 1) * (q ^ 12 - 1) := by
  have hg (d : ℕ) : (∑ k : Fin d, q ^ k.val) * (q - 1) = q ^ d - 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using geom_sum_mul_of_one_le hq d
  rw [rootWeylPoincareEval_E6_product]
  calc
    _ = ((∑ k : Fin 2, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 5, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 6, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 8, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 9, q ^ k.val) * (q - 1)) *
        ((∑ k : Fin 12, q ^ k.val) * (q - 1)) := by ring
    _ = _ := by rw [hg 2, hg 5, hg 6, hg 8, hg 9, hg 12]

end Atlas.Chevalley.E6D5
