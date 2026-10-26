import Atlas.LinearGroups.Chevalley.RootData.E6D5PoincareFactor
import Atlas.LinearGroups.Chevalley.RootData.ClassicalDPoincareProduct

/-! The actual E6 Weyl length polynomial, derived from its27 minimum
parabolic representatives and the proved D5 length polynomial. -/
noncomputable section
namespace Atlas.Chevalley.E6D5
open Classical RootData
local instance : Fintype E6Data.Root := Fintype.ofFinite _

theorem rootWeylPoincareEval_E6_product (q : ℕ) :
    rootWeylPoincareEval E6Data.pairing E6Data.base q =
      (∑ k : Fin 2, q ^ k.val) * (∑ k : Fin 5, q ^ k.val) *
      (∑ k : Fin 6, q ^ k.val) * (∑ k : Fin 8, q ^ k.val) *
      (∑ k : Fin 9, q ^ k.val) * (∑ k : Fin 12, q ^ k.val) := by
  have hg : (∑ k : Fin 4, q ^ k.val) * (1 + q ^ 4 + q ^ 8) =
      ∑ k : Fin 12, q ^ k.val := by
    simp only [Fin.sum_univ_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  rw [rootWeylPoincareEval_E6_D5, ClassicalDParabolic.rootWeylPoincareEval_D_product]
  norm_num only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.reduceAdd,
    Nat.reduceMul, one_mul]
  calc
    _ = (∑ k : Fin 2, q ^ k.val) * (∑ k : Fin 5, q ^ k.val) *
        (∑ k : Fin 6, q ^ k.val) * (∑ k : Fin 8, q ^ k.val) *
        (∑ k : Fin 9, q ^ k.val) *
        ((∑ k : Fin 4, q ^ k.val) * (1 + q ^ 4 + q ^ 8)) := by
          simp only [Fin.sum_univ_eq_sum_range]
          ring
    _ = _ := by rw [hg]

end Atlas.Chevalley.E6D5
