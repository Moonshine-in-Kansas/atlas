import Atlas.Rudvalis.CoupleFusionGroup
import Atlas.Rudvalis.CoordinateQuartetCompletion

namespace Atlas.Rudvalis

theorem coupleFusionGroup_preserves_intrinsicDozen (g : coupleFusionGroup) :
    gaussianImage g.val (intrinsicDozen referenceCouple)=intrinsicDozen referenceCouple := by
  rw [intrinsicDozen_gaussianImage,coupleFusionGroup_preserves_referenceCouple]

theorem coupleFusion_intrinsicDozen_iff (g : coupleFusionGroup) (c : MinimalCross) :
    g.val • c∈intrinsicDozen referenceCouple ↔ c∈intrinsicDozen referenceCouple := by
  simpa only [coupleFusionGroup_preserves_intrinsicDozen g] using
    gaussianImage_mem g.val (intrinsicDozen referenceCouple) c

theorem coupleFusion_orbit_avoids_intrinsicDozen (c : MinimalCross)
    (hc : c∉intrinsicDozen referenceCouple) :
    ∀z∈MulAction.orbit coupleFusionGroup c,z∉intrinsicDozen referenceCouple := by
  intro z hz
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hz
  exact fun h=>hc ((coupleFusion_intrinsicDozen_iff g c).mp h)

theorem outside_coordinate_not_intrinsicDozen (z : MinimalCross)
    (hzF : z∈coordinateFrame) (hzD : z∉referenceCoordinateDozen) :
    z∉intrinsicDozen referenceCouple :=
  reference_no_quartet_through_outside_coordinate z hzF hzD

theorem reference_intrinsicDozen_coordinate_intersection :
    intrinsicDozen referenceCouple∩coordinateFrame=referenceCoordinateDozen := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨Q,hQ,hc,hz⟩,hzF⟩
    exact reference_quartet_coordinate_member_in_dozen Q hQ hc z hz hzF
  · intro z hz
    exact ⟨referenceCoordinateDozen_subset_intrinsicDozen hz,referenceCoordinateDozen_subset hz⟩

theorem codeCouple_coordinateDozen_stable (g : codeCoupleStabilizer) (c : MinimalCross)
    (hc : c∈referenceCoordinateDozen) : g.val • c∈referenceCoordinateDozen := by
  rw [←reference_intrinsicDozen_coordinate_intersection]
  refine ⟨?_,coordinateFrame_code_stable g.val c (referenceCoordinateDozen_subset hc)⟩
  let a : coupleFusionGroup := ⟨coupleGaussianHom g,coupleGaussianHom_mem g⟩
  have h := (coupleFusion_intrinsicDozen_iff a c).mpr
    (referenceCoordinateDozen_subset_intrinsicDozen hc)
  change codeGaussianHom g.val • c∈intrinsicDozen referenceCouple at h
  rwa [codeGaussianHom_cross] at h

theorem codeCouple_coordinateDozen_iff (g : codeCoupleStabilizer) (c : MinimalCross) :
    g.val • c∈referenceCoordinateDozen ↔ c∈referenceCoordinateDozen := by
  constructor
  · intro h
    have hi := codeCouple_coordinateDozen_stable g⁻¹ (g.val • c) h
    simpa only [Subgroup.coe_inv,inv_smul_smul] using hi
  · exact codeCouple_coordinateDozen_stable g c

end Atlas.Rudvalis
