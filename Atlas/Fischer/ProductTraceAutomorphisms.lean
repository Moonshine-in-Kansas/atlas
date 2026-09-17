import Atlas.Fischer.ProductTraceSemilinear
import Atlas.Fischer.SemilinearAlgebraAutomorphisms

noncomputable section
namespace Atlas.Fischer

/-- The retained untagged algebra automorphism, equipped with its proved scalar action. -/
def productTraceAlgebraEquiv (e : SemilinearAlgebraAutomorphism) :
    Coordinates ≃ₛₗ[(scalarParityAut (semilinearAlgebraParity e)).toRingHom] Coordinates where
  toEquiv := e.val
  map_add' := e.property.1
  map_smul' := semilinearAlgebraParity_spec e

theorem productLeftComposite_algebra_conj (e : SemilinearAlgebraAutomorphism)
    (x y : Coordinates) :
    (productTraceAlgebraEquiv e).conj (productLeftComposite x y) =
      productLeftComposite (e.val x) (e.val y) := by
  apply LinearMap.ext
  intro z
  change e.val (product (product (e.val.symm z) y) x) =
    product (product z (e.val y)) (e.val x)
  rw [e.property.2.1,e.property.2.1,e.val.apply_symm_apply]

theorem productTrace_algebra_automorphism (e : SemilinearAlgebraAutomorphism)
    (x y : Coordinates) : productTrace (e.val x) (e.val y) =
      scalarParityAut (semilinearAlgebraParity e) (productTrace x y) := by
  unfold productTrace
  rw [← productLeftComposite_algebra_conj]
  exact productTrace_semilinear_conj _ _ _

/-- Intrinsic-form deduction, explicitly conditional on the still separate trace-98 computation. -/
theorem productTrace_intrinsic_form_of_identity
    (htrace : ∀ x y : Coordinates, productTrace x y = (98 : Scalar) * hermitian y x)
    (e : SemilinearAlgebraAutomorphism) (x y : Coordinates) :
    hermitian (e.val x) (e.val y) =
      scalarParityAut (semilinearAlgebraParity e) (hermitian x y) := by
  have h := productTrace_algebra_automorphism e y x
  rw [htrace,htrace,map_mul,map_ofNat] at h
  exact mul_left_cancel₀ (by norm_num : (98 : Scalar) ≠ 0) h

end Atlas.Fischer
