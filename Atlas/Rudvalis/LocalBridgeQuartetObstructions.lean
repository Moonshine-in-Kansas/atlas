import Atlas.Rudvalis.LocalTripleCrossObstruction

namespace Atlas.Rudvalis

theorem reference_no_quartet_transport (g : gaussianLatticeGroup)
    (hx : g • localReferenceCross=localReferenceCross)
    (hy : g • referenceSecondCross=referenceSecondCross)
    (z : MinimalCross)
    (hz : ¬∃Q : Set MinimalCross,IsQuartet Q ∧ referenceCouple⊆Q ∧ z∈Q) :
    ¬∃Q : Set MinimalCross,IsQuartet Q ∧ referenceCouple⊆Q ∧ g • z∈Q := by
  rintro ⟨Q,hQ,hc,hzQ⟩
  apply hz
  refine ⟨gaussianImage g⁻¹ Q,(isQuartet_gaussianImage _ _).mpr hQ,?_,?_⟩
  · rintro w (rfl|rfl)
    · have h := Set.mem_image_of_mem (fun c : MinimalCross => g⁻¹ • c) (hc (Or.inl rfl))
      change g⁻¹ • localReferenceCross∈gaussianImage g⁻¹ Q at h
      rw [←hx,inv_smul_smul] at h
      exact h
    · have h := Set.mem_image_of_mem (fun c : MinimalCross => g⁻¹ • c) (hc (Or.inr rfl))
      change g⁻¹ • referenceSecondCross∈gaussianImage g⁻¹ Q at h
      rw [←hy,inv_smul_smul] at h
      exact h
  · have h := Set.mem_image_of_mem (fun c : MinimalCross => g⁻¹ • c) hzQ
    change g⁻¹ • (g • z)∈gaussianImage g⁻¹ Q at h
    simpa only [inv_smul_smul] using h

noncomputable def localOutsideCoordinate : Coordinate := seedCoordinateEquiv (1,0)
noncomputable def localFourBridgeCross : MinimalCross :=
  localFusionT • coordinateCross localOutsideCoordinate
noncomputable def localHeavyBridgeCross : MinimalCross := localFusionT • shiftedSeedCross

theorem localOutsideCoordinate_not_dozen :
    coordinateCross localOutsideCoordinate∉referenceCoordinateDozen := by
  rintro ⟨p,hp,hc⟩
  have he := (coordinateCross_mem_row_iff localOutsideCoordinate.1 p localOutsideCoordinate.2).mp hc
  subst p
  have hn : localOutsideCoordinate.1∉referenceDozenRows := by
    change dot (binaryLabel 1) (rowLabel 1).val≠0
    decide +kernel
  exact hn hp

theorem localFourBridgeCross_no_quartet :
    ¬∃Q : Set MinimalCross,IsQuartet Q ∧ referenceCouple⊆Q ∧ localFourBridgeCross∈Q :=
  reference_no_quartet_transport localFusionT localFusionT_fixes_first localFusionT_fixes_second _
    (reference_no_quartet_through_outside_coordinate _ (coordinateCross_mem _) localOutsideCoordinate_not_dozen)

theorem localHeavyBridgeCross_no_quartet :
    ¬∃Q : Set MinimalCross,IsQuartet Q ∧ referenceCouple⊆Q ∧ localHeavyBridgeCross∈Q :=
  reference_no_quartet_transport localFusionT localFusionT_fixes_first localFusionT_fixes_second _
    shiftedSeedCross_no_quartet

end Atlas.Rudvalis
