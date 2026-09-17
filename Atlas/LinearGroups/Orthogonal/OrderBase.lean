import Atlas.LinearGroups.Orthogonal.Radical
import Atlas.LinearAlgebra.QuadraticScalar

/-! # Internal rank-zero bases for full orthogonal group orders -/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem rankZero_vectorB (x : VectorB 0 F) : x = x.2 • z := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · simp [z]

@[simp] theorem formB_zeroRank (x : VectorB 0 F) : formB 0 F x = x.2 ^ 2 := by
  simp [formB_apply, formD_apply]

/-- Full isometries of the final anisotropic line are exactly scalar signs. -/
def rankZeroBEquiv : O_B 0 F ≃ {a : F // a ^ 2 = 1} where
  toFun g := ⟨(g.val z).2, by
    have h := g.prop z
    simpa only [formB_zeroRank, z, one_pow] using h⟩
  invFun a := (isometryCarrierEquiv _).symm (Atlas.Quadratic.scalarIsometry (formB 0 F) a.val a.prop)
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change (g.val z).2 • x = g.val x
    calc
      (g.val z).2 • x = (g.val z).2 • (x.2 • z) := congrArg _ (rankZero_vectorB x)
      _ = x.2 • ((g.val z).2 • z) := smul_comm _ _ _
      _ = x.2 • g.val z := congrArg _ (rankZero_vectorB (g.val z)).symm
      _ = g.val (x.2 • z) := (map_smul g.val _ _).symm
      _ = g.val x := congrArg _ (rankZero_vectorB x).symm
  right_inv a := by
    apply Subtype.ext
    change (a.val • z (n := 0)).2 = a.val
    simp [z]

theorem card_fullB_zero : Nat.card (O_B 0 F) = if (2 : F) = 0 then 1 else 2 := by
  rw [Nat.card_congr rankZeroBEquiv, Atlas.Quadratic.card_squareOne]

theorem card_fullD_zero : Nat.card (O_DPlus 0 F) = 1 := by
  haveI : Subsingleton (O_DPlus 0 F) := ⟨fun g h => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_unique

end Atlas.Orthogonal
