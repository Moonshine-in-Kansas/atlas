import Atlas.LinearGroups.Chevalley.RootData.E7E6PoincareFactor
import Atlas.LinearGroups.Chevalley.RootData.E6PoincareProduct

/-! The actual E7 Weyl length polynomial from its56 minimum parabolic
representatives and the actual E6 degree polynomial. -/
namespace Atlas.Chevalley.E7E6
open RootData

theorem rootWeylPoincareEval_E7_product (q : ℕ) :
    rootWeylPoincareEval E7Data.pairing E7Data.base q =
      (∑ k : Fin 2, q ^ k.val) * (∑ k : Fin 6, q ^ k.val) *
      (∑ k : Fin 8, q ^ k.val) * (∑ k : Fin 10, q ^ k.val) *
      (∑ k : Fin 12, q ^ k.val) * (∑ k : Fin 14, q ^ k.val) *
      (∑ k : Fin 18, q ^ k.val) := by
  have h5 : (∑ k : Fin 5, q ^ k.val) * (1 + q ^ 5) =
      ∑ k : Fin 10, q ^ k.val := by
    simp only [Fin.sum_univ_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  have h9 : (∑ k : Fin 9, q ^ k.val) * (1 + q ^ 9) =
      ∑ k : Fin 18, q ^ k.val := by
    simp only [Fin.sum_univ_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  rw [rootWeylPoincareEval_E7_E6, E6D5.rootWeylPoincareEval_E6_product]
  calc
    _ = (∑ k : Fin 2, q ^ k.val) * (∑ k : Fin 6, q ^ k.val) *
        (∑ k : Fin 8, q ^ k.val) *
        ((∑ k : Fin 5, q ^ k.val) * (1 + q ^ 5)) *
        (∑ k : Fin 12, q ^ k.val) * (∑ k : Fin 14, q ^ k.val) *
        ((∑ k : Fin 9, q ^ k.val) * (1 + q ^ 9)) := by ac_rfl
    _ = _ := by rw [h5, h9]

end Atlas.Chevalley.E7E6
