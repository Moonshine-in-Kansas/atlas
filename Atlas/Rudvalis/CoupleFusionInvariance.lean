import Atlas.Rudvalis.CoupleFusionPieces

namespace Atlas.Rudvalis

theorem coupleFusion_dozen_iff (g : coupleFusionGroup) (c : MinimalCross) :
    g.val • c∈referenceCoordinateDozen ↔ c∈referenceCoordinateDozen := by
  rw [←reference_intrinsicDozen_eq]
  exact coupleFusion_intrinsicDozen_iff g c

theorem coupleFusion_reference_orthogonal_iff (g : coupleFusionGroup) (c : MinimalCross) :
    ReferenceCoupleOrthogonal (g.val • c) ↔ ReferenceCoupleOrthogonal c := by
  have hx := (coupleFusionGroup_fix g).1
  have hy := (coupleFusionGroup_fix g).2
  have h0 := crossOrthogonal_gaussian g.val localReferenceCross c
  have h1 := crossOrthogonal_gaussian g.val referenceSecondCross c
  rw [hx] at h0
  rw [hy] at h1
  exact and_congr h0 h1

theorem coupleFusionTen_stable (g : coupleFusionGroup) (c : MinimalCross)
    (hc : c∈coupleFusionTen) : g.val • c∈coupleFusionTen := by
  refine ⟨⟨(coupleFusion_dozen_iff g c).mpr hc.1.1,?_⟩,?_⟩
  · intro h
    apply hc.1.2
    apply MulAction.injective g.val
    exact h.trans (coupleFusionGroup_fix g).1.symm
  · intro h
    apply hc.2
    apply MulAction.injective g.val
    exact h.trans (coupleFusionGroup_fix g).2.symm

theorem coupleFusionEighty_stable (g : coupleFusionGroup) (c : MinimalCross)
    (hc : c∈coupleFusionEighty) : g.val • c∈coupleFusionEighty := by
  intro z hz
  have hi : g.val⁻¹ • z∈referenceCoordinateDozen :=
    (coupleFusion_dozen_iff g⁻¹ z).mpr hz
  have h := (crossOrthogonal_gaussian g.val (g.val⁻¹ • z) c).mpr (hc _ hi)
  simpa only [smul_inv_smul] using h

theorem coupleFusionEighty_iff (g : coupleFusionGroup) (c : MinimalCross) :
    g.val • c∈coupleFusionEighty ↔ c∈coupleFusionEighty := by
  constructor
  · intro h
    have hi := coupleFusionEighty_stable g⁻¹ (g.val • c) h
    simpa only [Subgroup.coe_inv,inv_smul_smul] using hi
  · exact coupleFusionEighty_stable g c

theorem coupleFusionSixForty_stable (g : coupleFusionGroup) (c : MinimalCross)
    (hc : c∈coupleFusionSixForty) : g.val • c∈coupleFusionSixForty :=
  ⟨(coupleFusion_reference_orthogonal_iff g c).mpr hc.1,
    fun h=>hc.2.1 ((coupleFusion_dozen_iff g c).mp h),
    fun h=>hc.2.2 ((coupleFusionEighty_iff g c).mp h)⟩

theorem coupleFusionThousand_stable (g : coupleFusionGroup) (c : MinimalCross)
    (hc : c∈coupleFusionThousand) : g.val • c∈coupleFusionThousand := by
  have hx := (coupleFusionGroup_fix g).1
  have hy := (coupleFusionGroup_fix g).2
  have h0 := crossOrthogonal_gaussian g.val localReferenceCross c
  have h1 := crossOrthogonal_gaussian g.val referenceSecondCross c
  rw [hx] at h0
  rw [hy] at h1
  refine ⟨⟨h0.mpr hc.1.1,fun h=>hc.1.2 (h1.mp h)⟩,?_⟩
  intro h
  apply hc.2
  apply MulAction.injective g.val
  exact h.trans hy.symm

end Atlas.Rudvalis
