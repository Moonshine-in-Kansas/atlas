import Atlas.Rudvalis.CoupleCoordinateOrbitSets
import Atlas.Rudvalis.LocalBridgeQuartetObstructions

namespace Atlas.Rudvalis

theorem localThirdCross_mem_coupleCoordinateTwo : localThirdCross∈coupleCoordinateTwo := by
  refine ⟨⟨localFusion_third_source_row,localThirdCross_ne_reference⟩,?_⟩
  change coordinateCross (localFusionSourceCoordinate 2)≠referenceSecondCross
  rw [referenceSecondCross_eq,ne_eq,coordinateCross_eq_iff,codeI_coordinate]
  decide +kernel

theorem localFusionT_third_mem_coupleCoordinateEight :
    localFusionT • localThirdCross∈coupleCoordinateEight := by
  change localFusionT • coordinateCross (localFusionSourceCoordinate 2)∈_
  rw [localFusionT_cross_action]
  refine ⟨?_,localFusion_third_target_not_row⟩
  refine ⟨rowLabel 4,(referenceDozenRows_marking 4).mpr (Or.inr (Or.inl rfl)),?_⟩
  exact ⟨(localFusionTargetCoordinate 2).2,rfl⟩

theorem localOutsideCoordinate_mem_coupleCoordinateSixteen :
    coordinateCross localOutsideCoordinate∈coupleCoordinateSixteen :=
  ⟨coordinateCross_mem _,localOutsideCoordinate_not_dozen⟩

end Atlas.Rudvalis
