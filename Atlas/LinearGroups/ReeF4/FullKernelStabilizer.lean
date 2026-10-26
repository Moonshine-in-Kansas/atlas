import Atlas.LinearGroups.ReeF4.PolynomialExterior
import Atlas.LinearGroups.ReeF4.DomainWedgeExt

/-! The intrinsic partial-product condition is exactly the condition on the full
polar/cross kernel; no isotropy restriction or selected wedge subset is used. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def PreservesCandidateKernel (σ : F →+* F)
    (g : traceZeroPolynomialStabilizer (F := F)) : Prop :=
  ∀ x : StarCarrier (F := F),
    proposedStarSemilinear σ (polynomialStarLinear g x) =
      g.val (proposedStarSemilinear σ x)

theorem preservesCandidatePartial_iff_kernel (σ : F →+* F)
    (g : traceZeroPolynomialStabilizer (F := F)) :
    PreservesCandidatePartial σ g ↔ PreservesCandidateKernel σ g := by
  constructor
  · intro h
    have he : (proposedStarSemilinear σ).comp (polynomialStarLinear g) =
        g.val.toLinearMap.comp (proposedStarSemilinear σ) := by
      apply domainWedge_semilinear_ext σ
      intro u v huv
      simp only [LinearMap.comp_apply, polynomialStarLinear_domainWedge]
      exact h u v huv
    intro x
    exact LinearMap.congr_fun he x
  · intro h u v huv
    have he := h (domainWedge u v huv)
    rw [polynomialStarLinear_domainWedge] at he
    exact he

end Atlas.ReeF4
