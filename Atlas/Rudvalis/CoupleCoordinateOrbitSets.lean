import Atlas.Rudvalis.CoupleCoordinateOrbits
import Atlas.Rudvalis.CoupleQuartetTransport

namespace Atlas.Rudvalis

noncomputable def coupleCoordinateTwo : Set MinimalCross :=
  (coordinateRowFrame (rowLabel 0)\{localReferenceCross})\{referenceSecondCross}
noncomputable def coupleCoordinateEight : Set MinimalCross :=
  referenceCoordinateDozen\coordinateRowFrame (rowLabel 0)
noncomputable def coupleCoordinateSixteen : Set MinimalCross :=
  coordinateFrame\referenceCoordinateDozen

 theorem codeCouple_row_iff (g : codeCoupleStabilizer) (c : MinimalCross) :
    g.val • c∈coordinateRowFrame (rowLabel 0) ↔ c∈coordinateRowFrame (rowLabel 0) := by
  have hs (g : codeCoupleStabilizer) (c) (hc : c∈coordinateRowFrame (rowLabel 0)) :
      g.val • c∈coordinateRowFrame (rowLabel 0) := by
    let a : MulAction.stabilizer codeGroup (coordinateCross (rowLabel 0,0)) :=
      ⟨g.val,by
        have h := g.prop.1
        change g.val • localReferenceCross=localReferenceCross at h
        change g.val • coordinateCross (rowLabel 0,0)=coordinateCross (rowLabel 0,0)
        rwa [localReferenceCross_eq] at h⟩
    exact coordinateCross_stabilizer_row_mem (rowLabel 0) 0 a c hc
  constructor
  · intro h; simpa using hs g⁻¹ (g.val • c) h
  · exact hs g c

private theorem coupleOrbit_eq (s : Set MinimalCross) (v : MinimalCross) (hv : v∈s)
    (hs : ∀g : codeCoupleStabilizer,∀c∈s,g.val • c∈s)
    (ht : ∀w∈s,∃g : codeCoupleStabilizer,g.val • v=w) :
    MulAction.orbit codeCoupleStabilizer v=s := by
  ext w
  constructor
  · intro h
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp h
    exact hs g v hv
  · intro h; exact MulAction.mem_orbit_iff.mpr (ht w h)

 theorem coupleCoordinateTwo_orbit (v : MinimalCross) (hv : v∈coupleCoordinateTwo) :
    MulAction.orbit codeCoupleStabilizer v=coupleCoordinateTwo := by
  apply coupleOrbit_eq _ _ hv
  · intro g c hc
    refine ⟨⟨(codeCouple_row_iff g c).mpr hc.1.1,?_⟩,?_⟩
    · intro h
      exact hc.1.2 (MulAction.injective g.val (h.trans g.prop.1.symm))
    · intro h
      exact hc.2 (MulAction.injective g.val (h.trans g.prop.2.symm))
  · intro w hw
    exact couple_coordinate_reference_row_transitive v w hv.1.1 hw.1.1 hv.1.2 hv.2 hw.1.2 hw.2

 theorem coupleCoordinateEight_orbit (v : MinimalCross) (hv : v∈coupleCoordinateEight) :
    MulAction.orbit codeCoupleStabilizer v=coupleCoordinateEight := by
  apply coupleOrbit_eq _ _ hv
  · intro g c hc
    exact ⟨codeCouple_coordinateDozen_stable g c hc.1,fun h=>hc.2 ((codeCouple_row_iff g c).mp h)⟩
  · intro w hw; exact couple_coordinate_dozen_other_rows_transitive v w hv hw

 theorem coupleCoordinateSixteen_orbit (v : MinimalCross) (hv : v∈coupleCoordinateSixteen) :
    MulAction.orbit codeCoupleStabilizer v=coupleCoordinateSixteen := by
  apply coupleOrbit_eq _ _ hv
  · intro g c hc
    exact ⟨coordinateFrame_code_stable g.val c hc.1,fun h=>hc.2 ((codeCouple_coordinateDozen_iff g c).mp h)⟩
  · intro w hw; exact couple_coordinate_outside_dozen_transitive v w hv hw

 theorem coordinate_reference_row_subset_dozen : coordinateRowFrame (rowLabel 0)⊆referenceCoordinateDozen := by
  intro c hc
  exact ⟨rowLabel 0,(referenceDozenRows_marking 0).mpr (Or.inl rfl),hc⟩

 theorem coupleCoordinateEight_card : Nat.card coupleCoordinateEight=8 := by
  change (referenceCoordinateDozen\coordinateRowFrame (rowLabel 0)).ncard=8
  rw [Set.ncard_sdiff coordinate_reference_row_subset_dozen]
  change Nat.card referenceCoordinateDozen-Nat.card (coordinateRowFrame (rowLabel 0))=8
  rw [referenceCoordinateDozen_card,coordinateRowFrame_card]

 theorem coupleCoordinateSixteen_card : Nat.card coupleCoordinateSixteen=16 :=
  referenceCoordinateDozen_outside_card

 theorem coupleCoordinateTwo_card : Nat.card coupleCoordinateTwo=2 := by
  have hx : localReferenceCross∈coordinateRowFrame (rowLabel 0) := by
    rw [localReferenceCross_eq]; exact ⟨0,rfl⟩
  have hy : referenceSecondCross∈coordinateRowFrame (rowLabel 0)\{localReferenceCross} := by
    refine ⟨?_,Ne.symm reference_crosses_ne⟩
    rw [referenceSecondCross_eq]; exact ⟨binaryLabel 2,rfl⟩
  change ((coordinateRowFrame (rowLabel 0)\{localReferenceCross})\{referenceSecondCross}).ncard=2
  rw [Set.ncard_sdiff_singleton_of_mem hy,Set.ncard_sdiff_singleton_of_mem hx]
  change Nat.card (coordinateRowFrame (rowLabel 0))-1-1=2
  rw [coordinateRowFrame_card]

end Atlas.Rudvalis
