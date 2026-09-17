import Atlas.LinearGroups.Orthogonal.ElementaryFieldTransport
import Atlas.LinearGroups.Orthogonal.ProjectiveElementary
import Atlas.LinearGroups.Orthogonal.IntrinsicStandard

/-! # Transport of actual scalar quotients and intrinsic odd kernels -/
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal
variable {F K V W : Type*} [Field F] [Field K]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module K W]
variable (e : F ≃+* K) (T : V ≃ₛₗ[RingHomClass.toRingHom e] W)
variable (Q : QuadraticForm F V) (R : QuadraticForm K W)
variable (hQ : ∀ x, R (T x) = e (Q x))

theorem semilinearElementaryEquiv_apply (g : elementarySubgroup Q) (x : W) :
    (semilinearElementaryEquiv e T Q R hQ g).val.val x = T (g.val.val (T.symm x)) := rfl

theorem semilinear_scalar_membership (g : elementarySubgroup Q) :
    g ∈ elementaryScalarSubgroup Q ↔
      semilinearElementaryEquiv e T Q R hQ g ∈ elementaryScalarSubgroup R := by
  constructor
  · rintro ⟨c, hc, hscalar⟩
    refine ⟨e c, by rw [← map_pow, hc, map_one], ?_⟩
    intro x
    rw [semilinearElementaryEquiv_apply, hscalar, map_smulₛₗ, T.apply_symm_apply]
    rfl
  · rintro ⟨d, hd, hscalar⟩
    refine ⟨e.symm d, by rw [← map_pow, hd, map_one], ?_⟩
    intro x
    apply T.injective
    have h := hscalar (T x)
    rw [semilinearElementaryEquiv_apply, T.symm_apply_apply] at h
    rw [map_smulₛₗ]
    change T (g.val.val x) = e (e.symm d) • T x
    rw [e.apply_symm_apply]
    exact h

theorem semilinear_scalar_map :
    (elementaryScalarSubgroup Q).map (semilinearElementaryEquiv e T Q R hQ).toMonoidHom =
      elementaryScalarSubgroup R := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (semilinear_scalar_membership e T Q R hQ z).mp hz
  · intro hg
    obtain ⟨z, rfl⟩ := (semilinearElementaryEquiv e T Q R hQ).surjective g
    exact ⟨z, (semilinear_scalar_membership e T Q R hQ z).mpr hg, rfl⟩

def semilinearProjectiveElementaryEquiv : ProjectiveElementary Q ≃* ProjectiveElementary R :=
  QuotientGroup.congr (elementaryScalarSubgroup Q) (elementaryScalarSubgroup R)
    (semilinearElementaryEquiv e T Q R hQ) (semilinear_scalar_map e T Q R hQ)

theorem semilinearProjectiveElementaryEquiv_mk (g : elementarySubgroup Q) :
    semilinearProjectiveElementaryEquiv e T Q R hQ (projectiveElementaryMap Q g) =
      projectiveElementaryMap R (semilinearElementaryEquiv e T Q R hQ g) := rfl

def fieldEquivProjectiveElementaryB
 {n : ℕ} (e : F ≃+* K) :
    ProjectiveElementary (formB n F) ≃* ProjectiveElementary (formB n K) :=
  semilinearProjectiveElementaryEquiv e (fieldCoordinatesB e) _ _ (fieldCoordinatesB_form e)

def fieldEquivProjectiveElementaryD {n : ℕ} (e : F ≃+* K) :
    ProjectiveElementary (formD n F) ≃* ProjectiveElementary (formD n K) :=
  semilinearProjectiveElementaryEquiv e (fieldCoordinatesD e) _ _ (fieldCoordinatesD_form e)

variable [Finite F] [Finite K]

def fieldEquivOddKernelB (n : ℕ) (e : F ≃+* K) (hF : (2 : F) ≠ 0) (hK : (2 : K) ≠ 0) :
    oddSpinorKernelB (n+2) hF ≃* oddSpinorKernelB (n+2) hK :=
  (elementaryB_kernelEquiv n hF).symm.trans
    ((fieldEquivElementaryB e).trans (elementaryB_kernelEquiv n hK))

def fieldEquivOddKernelD (n : ℕ) (e : F ≃+* K) (hF : (2 : F) ≠ 0) (hK : (2 : K) ≠ 0) :
    oddSpinorKernelD (n+2) hF ≃* oddSpinorKernelD (n+2) hK :=
  (elementaryD_kernelEquiv n hF).symm.trans
    ((fieldEquivElementaryD e).trans (elementaryD_kernelEquiv n hK))
theorem fieldEquivOddKernelB_full (n : ℕ) (e : F ≃+* K)
    (hF : (2 : F) ≠ 0) (hK : (2 : K) ≠ 0) (g : oddSpinorKernelB (n+2) hF) :
    (fieldEquivOddKernelB n e hF hK g).val.val = fieldEquivFullB e g.val.val := rfl

theorem fieldEquivOddKernelD_full (n : ℕ) (e : F ≃+* K)
    (hF : (2 : F) ≠ 0) (hK : (2 : K) ≠ 0) (g : oddSpinorKernelD (n+2) hF) :
    (fieldEquivOddKernelD n e hF hK g).val.val = fieldEquivFullD e g.val.val := rfl
end Atlas.Orthogonal

