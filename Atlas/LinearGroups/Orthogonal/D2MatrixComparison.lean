import Atlas.LinearGroups.Orthogonal.D2MatrixImage
import Atlas.LinearGroups.Orthogonal.D2MatrixSiegelImage
import Atlas.LinearGroups.Orthogonal.ProjectiveElementary

/-! # Actual split-D₂ comparison with the product of two projective special linear groups

The elementary image is identified through explicit generators in both directions.
Its projective kernel is the product of the two scalar centers. No order comparison,
source perfectness, or simplicity theorem is used, including over the binary field.
-/
noncomputable section
namespace Atlas.Orthogonal.D2Matrix
open Matrix
variable {F : Type*} [Field F]

theorem toOrthogonal_range : (toOrthogonal (F := F)).range = elementarySubgroup (formD 2 F) :=
  le_antisymm image_le_elementary elementary_le_image

def toElementary : PairSL (F := F) →* elementarySubgroup (formD 2 F) :=
  toOrthogonal.codRestrict _ toOrthogonal_mem_elementary

theorem toElementary_surjective : Function.Surjective (toElementary (F := F)) := by
  intro g
  obtain ⟨a,ha⟩ := elementary_le_image g.prop
  exact ⟨a,Subtype.ext ha⟩

def toProjective : PairSL (F := F) →* ProjectiveElementary (formD 2 F) :=
  (projectiveElementaryMap _).comp toElementary

theorem toProjective_surjective : Function.Surjective (toProjective (F := F)) :=
  (projectiveElementaryMap_surjective _).comp toElementary_surjective

theorem toProjective_eq_one_iff_centers (g : PairSL (F := F)) :
    toProjective g = 1 ↔ g.1 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∧
      g.2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  change (QuotientGroup.mk (toElementary g) : ProjectiveElementary (formD 2 F)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact toOrthogonal_scalar_iff_centers g

theorem toProjective_kernel : (toProjective (F := F)).ker =
    (Subgroup.center (SpecialLinearGroup (Fin 2) F)).prod
      (Subgroup.center (SpecialLinearGroup (Fin 2) F)) := by
  ext g
  exact toProjective_eq_one_iff_centers g

/-- The coordinatewise existing PSL₂ projections. -/
def productProjection : PairSL (F := F) →*
    ProjectiveSpecialLinearGroup (Fin 2) F × ProjectiveSpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))).prodMap
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)))

theorem productProjection_surjective : Function.Surjective (productProjection (F := F)) := by
  rintro ⟨x,y⟩
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin 2) F)) x
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin 2) F)) y
  exact ⟨(a,b),rfl⟩

theorem projective_kernels_eq : (toProjective (F := F)).ker = productProjection.ker := by
  ext g
  rw [MonoidHom.mem_ker, toProjective_eq_one_iff_centers]
  change _ ↔ ((QuotientGroup.mk g.1 : ProjectiveSpecialLinearGroup (Fin 2) F),
    (QuotientGroup.mk g.2 : ProjectiveSpecialLinearGroup (Fin 2) F)) = (1,1)
  rw [Prod.mk.injEq, QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]

/-- The actual projective elementary split-D₂ model is the product PSL₂ × PSL₂. -/
def projectiveEquivProduct : ProjectiveElementary (formD 2 F) ≃*
    ProjectiveSpecialLinearGroup (Fin 2) F × ProjectiveSpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientKerEquivOfSurjective toProjective toProjective_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq projective_kernels_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective productProjection productProjection_surjective))

/-- The isomorphism agrees with the original two matrix factors on every lift. -/
theorem projectiveEquivProduct_projection (g : PairSL (F := F)) :
    projectiveEquivProduct (projectiveElementaryMap _ (toElementary g)) =
      (QuotientGroup.mk g.1, QuotientGroup.mk g.2) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (toProjective (F := F)) toProjective_surjective
  change ((QuotientGroup.quotientMulEquivOfEq projective_kernels_eq).trans
    (QuotientGroup.quotientKerEquivOfSurjective productProjection productProjection_surjective))
      (e.symm (e (QuotientGroup.mk g))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Atlas.Orthogonal.D2Matrix
