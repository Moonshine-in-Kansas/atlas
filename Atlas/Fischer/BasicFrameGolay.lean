import Atlas.Fischer.BasicFrameAxes
import Atlas.Fischer.GeneratedCocode
import Atlas.Fischer.RootRayCovariance

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- A normalized basic-frame permutation conjugates the actual basic cocode
reflections, so all retained Golay relations are preserved. -/
theorem basicFrame_preserves_golay (e : SemilinearAlgebraAutomorphism)
    (σ : Equiv.Perm Omega) (he : ∀ i, e.val (basicAxis i) = basicAxis (σ i)) :
    CodePreserving σ := by
  have hg (i : Omega) :
      MulAut.conj e (cocodeAlgebraHom (cocodeInvolution i)) =
        cocodeAlgebraHom (cocodeInvolution (σ i)) := by
    rw [cocodeAlgebraHom_basic, cocodeAlgebraHom_basic]
    change e * reflectingRootAutomorphism (basicAxis i) _ * e⁻¹ =
      reflectingRootAutomorphism (basicAxis (σ i)) _
    rw [reflectingRootAutomorphism_conjugation]
    congr 1
    exact he i
  have hrel (S : Finset Omega) :
      binarySupportEquiv.symm S ∈ golay ↔ binarySupportEquiv.symm (S.image σ) ∈ golay := by
    rw [← cocodeAlgebraHom_relations, ← cocodeAlgebraHom_relations]
    have hprod : MulAut.conj e (cocodeAlgebraHom (∏ i ∈ S, cocodeInvolution i)) =
        cocodeAlgebraHom (∏ i ∈ S.image σ, cocodeInvolution i) := by
      classical
      induction S using Finset.induction_on with
      | empty => simp only [Finset.image_empty, Finset.prod_empty, map_one]
      | @insert i S hi ih =>
        have hi' : σ i ∉ S.image σ := by simpa only [Finset.mem_image, σ.injective.eq_iff, exists_eq_right] using hi
        rw [Finset.image_insert, Finset.prod_insert hi, Finset.prod_insert hi',
          map_mul, map_mul, map_mul, hg i, ih]
    constructor
    · intro h
      rw [← hprod, h, map_one]
    · intro h
      apply (MulAut.conj e).injective
      rw [hprod, h, map_one]
  intro w
  have hw : binarySupportEquiv.symm (support w) = w := binarySupportEquiv.symm_apply_apply w
  have hw' : binarySupportEquiv.symm ((support w).image σ) = coordinatePermutation σ w := by
    apply binarySupportEquiv.injective
    rw [binarySupportEquiv.apply_symm_apply]
    exact (coordinatePermutation_support σ w).symm
  simpa only [hw, hw'] using hrel (support w)

/-- Recover the actual retained Mathieu code automorphism, with precisely the
specified marked-coordinate permutation. -/
def basicFrameMathieu (e : SemilinearAlgebraAutomorphism) (σ : Equiv.Perm Omega)
    (he : ∀ i, e.val (basicAxis i) = basicAxis (σ i)) : Mathieu24CodeModel :=
  ⟨σ, basicFrame_preserves_golay e σ he⟩

@[simp] theorem basicFrameMathieu_apply (e : SemilinearAlgebraAutomorphism)
    (σ : Equiv.Perm Omega) (he : ∀ i, e.val (basicAxis i) = basicAxis (σ i)) (i : Omega) :
    (basicFrameMathieu e σ he).val i = σ i := rfl

end Atlas.Fischer
