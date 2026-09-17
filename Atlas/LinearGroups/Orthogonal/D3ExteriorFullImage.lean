import Atlas.LinearGroups.Orthogonal.D3ExteriorComparison
import Atlas.LinearGroups.Orthogonal.PerfectAllCharD

/-! # The full exterior-square image is exactly the actual elementary D₃ group

Projective surjectivity gives every elementary isometry as an image element
multiplied by a central scalar. Actual elementary perfectness removes the
central factor at the group level, without using any simplicity theorem.
-/
noncomputable section
namespace Atlas.Orthogonal.D3Exterior
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F]

/-- Every actual elementary isometry is an exterior-square image times a central scalar. -/
theorem image_mul_center (g : elementarySubgroup (formD 3 F)) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 4) F, ∃ z : elementarySubgroup (formD 3 F),
      z ∈ Subgroup.center (elementarySubgroup (formD 3 F)) ∧ g = toElementary a * z := by
  obtain ⟨x,hx⟩ := projectiveHom_surjective (projectiveElementaryMap _ g)
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F)) x
  change projectiveHom (QuotientGroup.mk a) = projectiveElementaryMap _ g at hx
  let z := (toElementary a)⁻¹ * g
  have hz : projectiveElementaryMap _ z = 1 := by
    change projectiveElementaryMap _ ((toElementary a)⁻¹ * g) = 1
    rw [map_mul, map_inv, ← projectiveHom_projection, hx, inv_mul_cancel]
  have hzs : z ∈ elementaryScalarSubgroup (formD 3 F) :=
    (QuotientGroup.eq_one_iff z).mp hz
  exact ⟨a,z,elementaryScalarSubgroup_le_center _ hzs,by simp [z]⟩

/-- Commutators of actual elementary isometries already belong to the full exterior-square image. -/
theorem commutator_le_image :
    commutator (elementarySubgroup (formD 3 F)) ≤ (toElementary (F := F)).range := by
  rw [commutator_eq_closure]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a,b,rfl⟩
  obtain ⟨u,z,hz,rfl⟩ := image_mul_center a
  obtain ⟨v,w,hw,rfl⟩ := image_mul_center b
  have hzcomm (x : elementarySubgroup (formD 3 F)) : ⁅z,x⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hz x).symm
  have hwcomm (x : elementarySubgroup (formD 3 F)) : ⁅x,w⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact Subgroup.mem_center_iff.mp hw x
  have he : ⁅toElementary u * z,toElementary v * w⁆ = ⁅toElementary u,toElementary v⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hzcomm, mul_one, mul_inv_cancel, one_mul,
      commutatorElement_mul_right_eq_mul_conj, hwcomm, mul_one, mul_inv_cancel_right]
  rw [he, ← map_commutatorElement]
  exact ⟨⁅u,v⁆,rfl⟩

/-- Surjectivity onto the actual elementary group, not only its scalar quotient. -/
theorem toElementary_surjective : Function.Surjective (toElementary (F := F)) := by
  letI := elementaryD_perfect_all_char (F := F) 0
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← Group.IsPerfect.commutator_eq_top]
  exact commutator_le_image

/-- Exact image of the original orthogonal homomorphism as a subgroup of actual O⁺₆. -/
theorem toOrthogonal_range :
    (toOrthogonal (F := F)).range = elementarySubgroup (formD 3 F) := by
  apply le_antisymm
  · rintro g ⟨a,rfl⟩
    exact toOrthogonal_mem_elementary a
  · intro g hg
    obtain ⟨a,ha⟩ := toElementary_surjective ⟨g,hg⟩
    exact ⟨a,congrArg Subtype.val ha⟩

end Atlas.Orthogonal.D3Exterior
