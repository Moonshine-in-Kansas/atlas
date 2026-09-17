import Atlas.LinearAlgebra.QuadraticScalar
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Scalar sign units and their cardinality over an arbitrary field -/
noncomputable section
open scoped Classical
namespace Atlas
variable {F : Type*} [Field F]

def squareOneUnitsEquiv : rootsOfUnity 2 F ≃ {a : F // a^2 = 1} where
  toFun a := ⟨a.val.val, by
    have h := (mem_rootsOfUnity 2 a.val).mp a.prop
    exact congrArg Units.val h⟩
  invFun a := ⟨Units.mk0 a.val (by
    intro h
    have ha := a.prop
    rw [h, zero_pow (by decide : 2 ≠ 0)] at ha
    exact zero_ne_one ha), by
      apply (mem_rootsOfUnity 2 _).mpr
      apply Units.ext
      exact a.prop⟩
  left_inv a := by apply Subtype.ext; apply Units.ext; rfl
  right_inv a := rfl

theorem card_squareOneUnits : Nat.card (rootsOfUnity 2 F) = if (2 : F) = 0 then 1 else 2 := by
  rw [Nat.card_congr squareOneUnitsEquiv, Atlas.Quadratic.card_squareOne]

end Atlas
