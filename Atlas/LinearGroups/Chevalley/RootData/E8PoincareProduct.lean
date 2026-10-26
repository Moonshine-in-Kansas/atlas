import Atlas.LinearGroups.Chevalley.RootData.E8E7PoincareFactor
import Atlas.LinearGroups.Chevalley.RootData.E7PoincareProduct
import Mathlib.Algebra.BigOperators.Fin

/-! The actual E8 Weyl degree product. The factors arise from the E7
parabolic and actual240-root quotient, not a supplied list of degrees. -/
namespace Atlas.Chevalley.E8E7
open RootData

private theorem geom_double (q d : ℕ) :
    (∑ k : Fin (d + d), q ^ k.val) = (∑ k : Fin d, q ^ k.val) * (1 + q ^ d) := by
  simp only [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_add]
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  ring

private theorem geom_twentyfour (q : ℕ) :
    (∑ k : Fin 24, q ^ k.val) =
      (∑ k : Fin 6, q ^ k.val) * (1 + q ^ 6 + q ^ 12 + q ^ 18) := by
  rw [show (∑ k : Fin 24, q ^ k.val) =
      (∑ k : Fin 12, q ^ k.val) * (1 + q ^ 12) from geom_double q 12,
    show (∑ k : Fin 12, q ^ k.val) =
      (∑ k : Fin 6, q ^ k.val) * (1 + q ^ 6) from geom_double q 6]
  ring

/-- Reassociate only abstract natural-number factors, before instantiating the
geometric sums. This avoids normalization through concrete root-data terms. -/
private theorem product_regroup
    (a2 a6 a8 a10 a12 a14 a18 a20 a24 a30 b6 b10 : ℕ)
    (h20 : a20 = a10 * b10) (h24 : a24 = a6 * b6) :
    (a30 * b6 * b10) * (a2 * a6 * a8 * a10 * a12 * a14 * a18) =
      a2 * a8 * a12 * a14 * a18 * a20 * a24 * a30 := by
  rw [h20, h24]
  ac_rfl

theorem rootWeylPoincareEval_E8_product (q : ℕ) :
    rootWeylPoincareEval E8Data.pairing E8Data.base q =
      (∑ k : Fin 2, q ^ k.val) * (∑ k : Fin 8, q ^ k.val) *
      (∑ k : Fin 12, q ^ k.val) * (∑ k : Fin 14, q ^ k.val) *
      (∑ k : Fin 18, q ^ k.val) * (∑ k : Fin 20, q ^ k.val) *
      (∑ k : Fin 24, q ^ k.val) * (∑ k : Fin 30, q ^ k.val) := by
  let g (d : ℕ) : ℕ := ∑ k : Fin d, q ^ k.val
  let f : ℕ := g 30 * (1 + q ^ 6 + q ^ 12 + q ^ 18) * (1 + q ^ 10)
  have h7 : f * rootWeylPoincareEval E7Data.pairing E7Data.base q =
      f * (g 2 * g 6 * g 8 * g 10 * g 12 * g 14 * g 18) :=
    congrArg (fun t : ℕ => f * t) (E7E6.rootWeylPoincareEval_E7_product q)
  have harith : f * (g 2 * g 6 * g 8 * g 10 * g 12 * g 14 * g 18) =
      g 2 * g 8 * g 12 * g 14 * g 18 * g 20 * g 24 * g 30 :=
    product_regroup (g 2) (g 6) (g 8) (g 10) (g 12) (g 14) (g 18)
      (g 20) (g 24) (g 30) (1 + q ^ 6 + q ^ 12 + q ^ 18) (1 + q ^ 10)
      (geom_double q 10) (geom_twentyfour q)
  exact (rootWeylPoincareEval_E8_E7 q).trans (h7.trans harith)

end Atlas.Chevalley.E8E7
