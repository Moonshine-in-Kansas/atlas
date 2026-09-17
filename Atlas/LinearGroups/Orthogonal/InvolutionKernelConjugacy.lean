import Atlas.LinearAlgebra.QuadraticInvolutionConjugacy
import Atlas.LinearGroups.Orthogonal.InvolutionCentralizerCorrection
import Atlas.GroupTheory.KernelConjugacyCorrection

/-! # Orthogonal and intrinsic-kernel conjugacy of involutions -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic Atlas.LinearInvolution
variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

theorem involution_conjugator_of_minus_dimension_spinor
    (t s : isometrySubgroup Q) (ht : Function.Involutive t.val) (hs : Function.Involutive s.val)
    (hd : Module.finrank F (minus t.val.toLinearMap) = Module.finrank F (minus s.val.toLinearMap))
    (hc : spinorNorm Q hQ h2 t = spinorNorm Q hQ h2 s) :
    ∃ k : isometrySubgroup Q, k*t*k⁻¹ = s := by
  letI := invertibleOfNonzero h2
  obtain ⟨k,hk⟩ := involution_conjugator_of_wallClass Q (isometryCarrierEquiv Q t) hQ
    (isometryCarrierEquiv Q s) ht hs hd hc
  change ∀ x : V, k (t.val x) = s.val (k x) at hk
  refine ⟨(isometryCarrierEquiv Q).symm k, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change k (t.val (k.symm x)) = s.val x
  rw [hk]
  change s.val (k (k.symm x)) = s.val x
  rw [k.apply_symm_apply]

/-- Full orthogonal conjugacy does not split inside the simultaneous determinant
and spinor kernel when the minus eigenspace has dimension at least two. -/
theorem involution_intrinsic_kernel_conjugator
    (t s : isometrySubgroup Q) (ht : Function.Involutive t.val) (hs : Function.Involutive s.val)
    (hd : Module.finrank F (minus t.val.toLinearMap) = Module.finrank F (minus s.val.toLinearMap))
    (hmin : 2 ≤ Module.finrank F (minus t.val.toLinearMap))
    (hc : spinorNorm Q hQ h2 t = spinorNorm Q hQ h2 s) :
    ∃ k : isometrySubgroup Q,
      k ∈ specialSubgroup Q ⊓ (spinorNorm Q hQ h2).ker ∧ k*t*k⁻¹ = s := by
  obtain ⟨g,hg⟩ := involution_conjugator_of_minus_dimension_spinor Q hQ h2 t s ht hs hd hc
  let φ := (determinant Q).prod (spinorNorm Q hQ h2)
  obtain ⟨c,hcomm,hdc,hsc⟩ := involution_centralizer_correction Q hQ h2 t ht hmin g
  have hφ : φ c = φ g := Prod.ext hdc hsc
  obtain ⟨k,hk,hconj⟩ := Atlas.kernel_conjugator_of_centralizer_image φ t s g hg
    ⟨c,hcomm.symm.eq,hφ⟩
  refine ⟨k, ?_, hconj⟩
  exact ⟨congrArg Prod.fst hk,congrArg Prod.snd hk⟩

end Atlas.Orthogonal
