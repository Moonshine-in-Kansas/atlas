import Atlas.LinearGroups.Orthogonal.B2ExteriorSymplectic
import Atlas.LinearGroups.Symplectic.Center

/-! # Scalar compatibility of the actual exterior-square homomorphism -/
noncomputable section
namespace Atlas.Orthogonal.B2Exterior
open Matrix
variable {F : Type*} [Field F]

theorem symplecticCoordinates_injective :
    Function.Injective (symplecticCoordinates (F := F)) := by
  intro u v h
  rw [symplecticCoordinates_eq, symplecticCoordinates_eq] at h
  funext i
  have he := congrFun h ((finSumFinEquiv : Atlas.Symplectic.Index 2 ≃ Fin 4) i)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using he

theorem symplecticMatrix_scalar_action (g : Atlas.Symplectic.Sp 2 F) (c : F)
    (hc : symplecticMatrix g = c • (1 : Matrix (Fin 4) (Fin 4) F)) :
    ∀ v : Atlas.Symplectic.Vector 2 F, g • v = c • v := by
  intro v
  apply symplecticCoordinates_injective
  change symplecticCoordinates (g.val *ᵥ v) = symplecticCoordinates (c • v)
  rw [← symplecticMatrix_mulVec, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  funext j
  simp only [symplecticCoordinates_eq, Function.comp_apply, Pi.smul_apply]

theorem exteriorMap_scalar (c : F) :
    exteriorMap (c • (1 : Matrix (Fin 4) (Fin 4) F)) = c^2 • LinearMap.id := by
  apply exterior_ext
  intro u v
  rw [exteriorMap_wedge]
  ext i
  fin_cases i <;> simp [Matrix.smul_mulVec, wedge, pow_two] <;> ring

theorem toOrthogonal_eq_one_of_center (g : Atlas.Symplectic.Sp 2 F)
    (hg : g ∈ Subgroup.center (Atlas.Symplectic.Sp 2 F)) : toOrthogonal g = 1 := by
  obtain ⟨c, hc, hcg⟩ := (Atlas.Symplectic.mem_center_iff_scalar (by decide : 0 < 2) g).mp hg
  have hm : symplecticMatrix g = c • (1 : Matrix (Fin 4) (Fin 4) F) := by
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨v, hv⟩ := symplecticCoordinates_surjective (F := F) (Pi.single i 1)
    rw [← hv, symplecticMatrix_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change symplecticCoordinates (g • v) = c • symplecticCoordinates v
    rw [hcg]
    funext j
    simp only [symplecticCoordinates_eq, Function.comp_apply, Pi.smul_apply]
  have he : exteriorMap (symplecticMatrix g) = LinearMap.id := by
    rw [hm, exteriorMap_scalar, hc, one_smul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change kernelEquiv.symm (kernelMap g (kernelEquiv v)) = v
  have hk : kernelMap g (kernelEquiv v) = kernelEquiv v := by
    apply Subtype.ext
    change exteriorMap (symplecticMatrix g) (kernelEquiv v).val = _
    rw [he, LinearMap.id_apply]
  rw [hk, LinearEquiv.symm_apply_apply]
end Atlas.Orthogonal.B2Exterior
