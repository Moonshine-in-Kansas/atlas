import Atlas.LinearGroups.ReeF4.RootGroupLinear
import Atlas.LinearGroups.ReeF4.Twist

/-! Actual invertible paired root operators over the admissible finite fields. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def shortRootPairEquiv (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    TraceZero F ≃ₗ[F] TraceZero F :=
  LinearEquiv.ofLinearMap (shortRootPairLinear (theta F m).toRingHom a b)
    (shortRootPairLinear (theta F m).toRingHom a (b+a*theta F m a))
    (shortRootPairLinear_inverse _ a b (SuzukiFamily.theta_square hcard a))
    (shortRootPairLinear_inverse_left _ a b (SuzukiFamily.theta_square hcard a))

@[simp] theorem shortRootPairEquiv_apply (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (w : TraceZero F) :
    shortRootPairEquiv m hcard a b w = shortRootPairLinear (theta F m).toRingHom a b w := rfl

@[simp] theorem shortRootPairEquiv_toLinearMap (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) :
    (shortRootPairEquiv m hcard a b).toLinearMap =
      shortRootPairLinear (theta F m).toRingHom a b := rfl

theorem shortRootPairEquiv_zero (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    shortRootPairEquiv m hcard (0:F) 0 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  change shortRootPairLinear (theta F m).toRingHom 0 0 = 1
  exact shortRootPairLinear_zero _

theorem shortRootPairEquiv_mul (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b c d : F) :
    shortRootPairEquiv m hcard a b * shortRootPairEquiv m hcard c d =
      shortRootPairEquiv m hcard (a+c) (b+d+theta F m a*c) := by
  apply LinearEquiv.toLinearMap_injective
  change shortRootPairLinear (theta F m).toRingHom a b *
      shortRootPairLinear (theta F m).toRingHom c d =
    shortRootPairLinear (theta F m).toRingHom (a+c) (b+d+theta F m a*c)
  exact shortRootPairLinear_mul _ a b c d (SuzukiFamily.theta_square hcard a)

theorem shortRootPairEquiv_inv (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    (shortRootPairEquiv m hcard a b)⁻¹ =
      shortRootPairEquiv m hcard a (b+a*theta F m a) := by
  apply LinearEquiv.ext
  intro w
  rfl

end Atlas.ReeF4
