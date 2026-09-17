import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Tactic

/-! # Scalar quadratic isometries and the two possible scalar signs -/
noncomputable section
open scoped Classical
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

def scalarIsometry (Q : QuadraticForm F V) (a : F) (ha : a ^ 2 = 1) : Q.IsometryEquiv Q where
  toFun x := a • x
  invFun x := a • x
  left_inv x := by
    change a • (a • x) = x
    rw [smul_smul, ← pow_two, ha, one_smul]
  right_inv x := by
    change a • (a • x) = x
    rw [smul_smul, ← pow_two, ha, one_smul]
  map_add' := smul_add a
  map_smul' b x := smul_comm a b x
  map_app' x := by rw [Q.map_smul, smul_eq_mul, ← pow_two, ha, one_mul]

/-- The scalar square roots of one are exactly the two displayed signs. -/
def squareOneEquivSigns : {a : F // a ^ 2 = 1} ≃ (↑({1, -1} : Finset F) : Type _) where
  toFun a := ⟨a.val, by simpa only [Finset.mem_insert, Finset.mem_singleton] using sq_eq_one_iff.mp a.prop⟩
  invFun a := ⟨a.val, sq_eq_one_iff.mpr (by simpa only [Finset.mem_insert, Finset.mem_singleton] using a.prop)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_squareOne : Nat.card {a : F // a ^ 2 = 1} = if (2 : F) = 0 then 1 else 2 := by
  classical
  rw [Nat.card_congr (squareOneEquivSigns (F := F)), Nat.card_eq_fintype_card, Fintype.card_coe]
  by_cases h : (2 : F) = 0
  · have hsign : (1 : F) = -1 := by linear_combination h
    rw [Finset.card_insert_of_mem (Finset.mem_singleton.mpr hsign), Finset.card_singleton, if_pos h]
  · have hsign : (1 : F) ≠ -1 := by intro he; apply h; linear_combination he
    rw [if_neg h]
    exact Finset.card_pair_eq_two_iff.mpr hsign

end Atlas.Quadratic
