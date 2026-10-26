import Atlas.LinearGroups.ReeF4.ExteriorSpanning

/-! All linear relations in the finite spanning family are given by the section. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem starProjection_eq_zero_iff (x : ⋀[F]^2 (TraceZero F)) :
    starProjection x = 0 ↔ x = exteriorJointSection (exteriorJoint x) := by
  rw [← Subtype.val_inj]
  change x - exteriorJointSection (exteriorJoint x) = 0 ↔ _
  exact sub_eq_zero

theorem starProjection_section (p : F × TraceZero F) :
    starProjection (exteriorJointSection p) = 0 := by
  rw [starProjection_eq_zero_iff, exteriorJoint_section]

theorem starProjection_ker : (starProjection (F := F)).ker = exteriorJointSection.range := by
  ext x
  rw [LinearMap.mem_ker, starProjection_eq_zero_iff]
  constructor
  · intro h
    exact ⟨exteriorJoint x, h.symm⟩
  · rintro ⟨p, rfl⟩
    rw [exteriorJoint_section]

theorem starSpanning_relation_iff (a : ExteriorIndex → F) :
    (∑ i, a i • starSpanning (F := F) i = 0) ↔
      ∃ p : F × TraceZero F, ∑ i, a i • markedExteriorBasis (F := F) i = exteriorJointSection p := by
  have h : starProjection (∑ i, a i • markedExteriorBasis (F := F) i) =
      ∑ i, a i • starSpanning (F := F) i := by simp only [_root_.map_sum, _root_.map_smul, starSpanning]
  rw [← h, ← LinearMap.mem_ker, starProjection_ker, LinearMap.mem_range]
  exact exists_congr (fun p => eq_comm)

/-- The section is injective, so it parametrizes relations without redundancy. -/
theorem exteriorJointSection_injective :
    Function.Injective (exteriorJointSection (F := F)) :=
  Function.LeftInverse.injective exteriorJoint_section

end Atlas.ReeF4
