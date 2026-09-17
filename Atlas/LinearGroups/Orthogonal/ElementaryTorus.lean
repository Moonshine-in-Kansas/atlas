import Atlas.LinearGroups.Orthogonal.HyperbolicTorus
import Atlas.LinearGroups.Orthogonal.IntrinsicKernelIdentification
import Atlas.LinearGroups.Orthogonal.RootSubgroupCoordinates

/-! # Square-parameter hyperbolic tori lie in the actual elementary group -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
variable (e f : V) (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include H hQ h2 in
theorem squareTorus_mem_elementary [Finite F] (a : F) (ha : a ≠ 0) :
    hyperbolicTorus Q e f he hf hef (a^2) (pow_ne_zero 2 ha) ∈ elementarySubgroup Q := by
  apply (elementary_eq_intrinsicKernel Q H hQ h2).ge
  constructor
  · change determinant Q (hyperbolicTorus Q e f he hf hef (a^2) _) = 1
    simp only [hyperbolicTorus, map_mul, hyperbolicReflection,
      reflectionElement_determinant, neg_mul_neg, one_mul]
  · change spinorNorm Q hQ h2 (hyperbolicTorus Q e f he hf hef (a^2) _) = 1
    simp only [hyperbolicTorus, map_mul, hyperbolicReflection, spinorNorm_reflection]
    have h₁ : Units.mk0 (Q (e+(1 : F) • f)) (ne_of_eq_of_ne (hyperbolic_reflection_norm Q e f he hf hef 1) one_ne_zero) = (1 : Fˣ) :=
      Units.ext (hyperbolic_reflection_norm Q e f he hf hef 1)
    have h₂ : Units.mk0 (Q (e+a^2 • f)) (ne_of_eq_of_ne (hyperbolic_reflection_norm Q e f he hf hef (a^2)) (pow_ne_zero 2 ha)) = (Units.mk0 a ha)^2 := by
      apply Units.ext
      exact hyperbolic_reflection_norm Q e f he hf hef (a^2)
    rw [h₁, h₂, map_one, one_mul, Atlas.squareClass_square]

theorem torus_root_conj (c : F) (hc : c ≠ 0) (w : complement Q e f) :
    hyperbolicTorus Q e f he hf hef c hc * rootComplementHom Q e f he (Multiplicative.ofAdd w) *
      (hyperbolicTorus Q e f he hf hef c hc)⁻¹ =
        rootComplementHom Q e f he (Multiplicative.ofAdd (c • w)) := by
  change _ * siegelElement Q e w.val he _ * _ = _
  rw [siegelElement_conj]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change siegel Q ((hyperbolicTorus Q e f he hf hef c hc).val e)
    ((hyperbolicTorus Q e f he hf hef c hc).val w.val) x = siegel Q e (c • w.val) x
  rw [hyperbolicTorus_e, hyperbolicTorus_perp]
  exact siegel_scale Q e w.val x c

end Atlas.Orthogonal
