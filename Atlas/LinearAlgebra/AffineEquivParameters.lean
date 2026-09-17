import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.SetTheory.Cardinal.Finite

namespace Atlas.LinearAlgebra

variable (F V : Type*) [Field F] [AddCommGroup V] [Module F V]

/-- An affine automorphism is determined by its translation and linear part. -/
def affineEquivParameters : (V ≃ᵃ[F] V) ≃ V × (V ≃ₗ[F] V) where
  toFun a := (a 0,a.linear)
  invFun p := AffineEquiv.ofLinearEquiv p.2 0 p.1
  left_inv a := by
    ext v
    change a.linear (v-0)+a 0=a v
    simpa using (a.map_vadd (0 : V) v).symm
  right_inv p := by
    apply Prod.ext
    · simp
    · rfl

theorem affineEquiv_card : Nat.card (V ≃ᵃ[F] V) = Nat.card V * Nat.card (V ≃ₗ[F] V) := by
  rw [Nat.card_congr (affineEquivParameters F V),Nat.card_prod]

end Atlas.LinearAlgebra
