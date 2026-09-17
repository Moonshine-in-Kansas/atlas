import Atlas.Fischer.ReflectionCalculus

noncomputable section
namespace Atlas.Fischer

/-- The image across a zero-pairing edge remains orthogonal to its source. -/
theorem reflectingRoot_zero_image_pairing (r s : Coordinates) (hs : IsReflectingRoot s)
    (h : hermitian r s=0) : hermitian s (rootMap r s)=0 := by
  rw [rootMap_zero_pairing r s h]
  change cubic s r s=0
  rw [cubic_swap_first s r s]
  change hermitian r (product s s)=0
  rw [hs.1.2,hermitian_smul_right,h,mul_zero]

/-- A zero-pairing root reflection moves the ray; this supplies the needed
nontriviality rather than inferring exact order from a power identity. -/
theorem reflectingRoot_zero_moves_ray (r s : Coordinates) (hs : IsReflectingRoot s)
    (h : hermitian r s=0) : rootRay (rootMap r s) ≠ rootRay s := by
  intro he
  obtain ⟨a,ha,he⟩ := (rootRay_eq_iff s (rootMap r s)).mp he
  have hz := reflectingRoot_zero_image_pairing r s hs h
  rw [he,hermitian_smul_right,hs.1.1] at hz
  have han : a ≠ 0 := by intro hn; rw [hn] at ha; norm_num at ha
  exact mul_ne_zero (star_ne_zero.mpr han) (by norm_num) hz

theorem reflectingRoot_unit_fixes_ray (r s : Coordinates) (hr : IsReflectingRoot r)
    (hs : IsReflectingRoot s) (h : hermitian r s ^ 3=1) :
    rootRay (rootMap r s)=rootRay s := by
  rw [nonorthogonal_root_rigidity r s hr.1 hs.1 hr.2.1 h]
  apply rootRay_phase
  rw [← star_pow,h,star_one]

/-- The exact fixed-ray criterion includes equal rays and requires no order,
transitivity, finite-family or separation assumption. -/
theorem reflectingRoot_fixed_ray_iff (r s : Coordinates) (hr : IsReflectingRoot r)
    (hs : IsReflectingRoot s) : rootRay (rootMap r s)=rootRay s ↔ hermitian r s ≠ 0 := by
  constructor
  · intro hf hz
    exact reflectingRoot_zero_moves_ray r s hs hz hf
  · intro hn
    by_cases he : rootRay s=rootRay r
    · obtain ⟨a,ha,rfl⟩ := (rootRay_eq_iff r s).mp he
      rw [rootMap_input_phase_ray r r a ha,reflectingRoot_rootMap_self r hr,rootRay_phase r a ha]
    · rcases reflectingRoot_distinct_ray_pairing r s hr hs he with hz | ⟨a,ha⟩
      · exact (hn hz).elim
      · apply reflectingRoot_unit_fixes_ray r s hr hs
        rw [ha]
        exact (mem_rootsOfUnity' _ _).mp a.property

end Atlas.Fischer
