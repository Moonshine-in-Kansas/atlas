import Atlas.Fischer.RootMomentRepresentativeIndependence
import Atlas.Fischer.RootRays
import Atlas.Fischer.SignedMonomialGeometry

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A parity-semilinear map permuting a spanning family up to cubic phases is
already invertible; invertibility is not an additional premise. -/
theorem rootRayPermutation_bijective {J : Type*} [Fintype J]
    (r : J → Coordinates) (hspan : Submodule.span Scalar (Set.range r)=⊤)
    (b : Bit) (g : Coordinates →ₛₗ[(scalarParityAut b).toRingHom] Coordinates)
    (π : Equiv.Perm J) (a : J → Mu3)
    (hg : ∀ j, g (r j)=(a j).val.val • r (π j)) : Function.Bijective g := by
  have hsur : Function.Surjective g := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    obtain ⟨k,rfl⟩ := π.surjective j
    change r (π k) ∈ g.range
    have hm : (a k).val.val • r (π k) ∈ g.range := ⟨r k,hg k⟩
    have hi := g.range.smul_mem (((a k).val : Scalar)⁻¹) hm
    simpa only [smul_smul,inv_mul_cancel₀ (Units.ne_zero (a k).val),one_smul] using hi
  let gg : Module.End Scalar Coordinates :=
    { toFun := fun x => g (g x)
      map_add' := by intro x y; rw [map_add,map_add]
      map_smul' := by
        intro c x
        rw [map_smulₛₗ,map_smulₛₗ]
        change scalarParityAut b (scalarParityAut b c) • g (g x)=c • g (g x)
        rw [scalarParityAut_involutive] }
  have hgg : Function.Surjective gg := hsur.comp hsur
  have hinj : Function.Injective gg := LinearMap.injective_iff_surjective.mpr hgg
  exact ⟨fun x y h => hinj (congrArg g h),hsur⟩

/-- The semilinear equivalence induced by an actual phase permutation. -/
def rootRayPermutationEquiv {J : Type*} [Fintype J]
    (r : J → Coordinates) (hspan : Submodule.span Scalar (Set.range r)=⊤)
    (b : Bit) (g : Coordinates →ₛₗ[(scalarParityAut b).toRingHom] Coordinates)
    (π : Equiv.Perm J) (a : J → Mu3)
    (hg : ∀ j, g (r j)=(a j).val.val • r (π j)) :
    Coordinates ≃ₛₗ[(scalarParityAut b).toRingHom] Coordinates :=
  LinearEquiv.ofBijective g (rootRayPermutation_bijective r hspan b g π a hg)

end Atlas.Fischer
