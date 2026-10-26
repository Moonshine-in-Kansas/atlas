import Atlas.LinearGroups.Chevalley.RootData.F4B3Parabolic
import Atlas.LinearGroups.Chevalley.RootData.F4ParabolicRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBCPoincareProduct
import Mathlib.Algebra.BigOperators.Fin

/-! The degrees2,6,8,12 are derived from the actual F4/B3 parabolic length
factorization. This is a statement about the original root-permutation Weyl
sum; no old F4 group cardinality or recognition result occurs. -/
noncomputable section
namespace Atlas.Chevalley.F4B3
open Classical ClassicalData RootData F4Data
local instance : Fintype (ClassicalBParabolic.W 2) := Fintype.ofFinite _
local instance : Fintype (rootParabolicSubgroup pairing base F4ShortOrbit.J) :=
  Fintype.ofFinite _

theorem rootWeylPoincareEval_F4_B3 (q : ℕ) :
    rootWeylPoincareEval pairing base q =
      ((∑ k : Fin 12, q ^ k.val) * (1 + q ^ 4)) *
        rootWeylPoincareEval (pairingB 3) (baseB 2) q := by
  have hs : (∑ w : rootParabolicSubgroup pairing base F4ShortOrbit.J,
      q ^ rootWeylLength pairing base w.val) =
        rootWeylPoincareEval (pairingB 3) (baseB 2) q := by
    calc
      _ = ∑ w : ClassicalBParabolic.W 2,
          q ^ rootWeylLength pairing base (parabolicEquiv.toEquiv w).val :=
        (Equiv.sum_comp parabolicEquiv.toEquiv
          (fun x => q ^ rootWeylLength pairing base x.val)).symm
      _ = ∑ w : ClassicalBParabolic.W 2,
          q ^ rootWeylLength (pairingB 3) (baseB 2) w := by
        apply Finset.sum_congr rfl
        intro w hw
        change q ^ rootWeylLength pairing base (parabolicEquiv w).val = _
        exact congrArg (fun n : ℕ => q ^ n) (parabolicEquiv_length w)
      _ = _ := rfl
  rw [F4ShortOrbit.rootWeylPoincareEval_F4_parabolic, hs]

private theorem geom_sum_eight (q : ℕ) :
    (∑ k : Fin 8, q ^ k.val) = (∑ k : Fin 4, q ^ k.val) * (1 + q ^ 4) := by
  simp only [Fin.sum_univ_eq_sum_range]
  rw [show 8 = 4 + 4 by rfl, Finset.sum_range_add]
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  ring

/-- Actual F4 Poincare degree product, for every natural evaluation parameter. -/
theorem rootWeylPoincareEval_F4_product (q : ℕ) :
    rootWeylPoincareEval pairing base q =
      (∑ k : Fin 2, q ^ k.val) * (∑ k : Fin 6, q ^ k.val) *
        (∑ k : Fin 8, q ^ k.val) * (∑ k : Fin 12, q ^ k.val) := by
  rw [rootWeylPoincareEval_F4_B3, ClassicalBParabolic.rootWeylPoincareEval_B_product]
  norm_num only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    Nat.reduceAdd, Nat.reduceMul]
  rw [geom_sum_eight]
  ring

end Atlas.Chevalley.F4B3
