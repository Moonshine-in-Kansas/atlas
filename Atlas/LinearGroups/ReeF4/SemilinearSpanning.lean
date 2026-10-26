import Atlas.LinearGroups.ReeF4.ExteriorRelations

/-! Semilinear maps are determined by the complete finite domain presentation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
variable {R : Type*} [CommRing R] (σ : F →+* R)
variable {M : Type*} [AddCommGroup M] [Module R M]

theorem starSpanning_semilinear_ext
    (f g : StarCarrier (F := F) →ₛₗ[σ] M)
    (h : ∀ i, f (starSpanning i) = g (starSpanning i)) : f = g := by
  apply LinearMap.ext
  intro x
  rw [← starSpanning_sum x]
  simp only [_root_.map_sum, LinearMap.map_smulₛₗ, h]

/-- Evaluate proposed spanning values on the canonical coordinates of a domain vector.
Agreement with the proposed values still requires the relation checks. -/
def fromSpanningValues (v : ExteriorIndex → M) : StarCarrier (F := F) →ₛₗ[σ] M where
  toFun x := ∑ i, σ ((markedExteriorBasis.repr x.val) i) • v i
  map_add' x y := by
    simp only [Submodule.coe_add, _root_.map_add, Finsupp.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Submodule.coe_smul, _root_.map_smul, Finsupp.smul_apply, smul_eq_mul,
      _root_.map_mul, mul_smul, Finset.smul_sum]

theorem fromSpanningValues_of_map (f : StarCarrier (F := F) →ₛₗ[σ] M) :
    fromSpanningValues σ (fun i => f (starSpanning i)) = f := by
  apply LinearMap.ext
  intro x
  have h := congrArg f (starSpanning_sum x)
  simpa only [fromSpanningValues, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.map_sum, LinearMap.map_smulₛₗ] using h

end Atlas.ReeF4
