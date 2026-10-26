import Atlas.Rudvalis.CoupleFusionInvariance
import Atlas.Rudvalis.CoupleCoordinateBridgeMembership
import Atlas.Rudvalis.LocalBridgeCommonEnergy

namespace Atlas.Rudvalis

private theorem coupleFusion_orbit_union (S T U : Set MinimalCross) (a b : MinimalCross)
    (hS : MulAction.orbit codeCoupleStabilizer a=S)
    (hT : MulAction.orbit codeCoupleStabilizer b=T)
    (hU : U=S∪T) (hb : b∈MulAction.orbit coupleFusionGroup a)
    (hstable : ∀g : coupleFusionGroup,∀c∈U,g.val • c∈U) :
    MulAction.orbit coupleFusionGroup a=U := by
  have ha : a∈U := by
    rw [hU,←hS]; exact Or.inl (MulAction.mem_orbit_self _)
  ext c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    exact hstable g a ha
  · intro hc
    rw [hU] at hc
    rcases hc with hc|hc
    · exact codeCoupleOrbit_subset_coupleFusionOrbit a (hS.symm ▸ hc)
    · have he : MulAction.orbit coupleFusionGroup b=MulAction.orbit coupleFusionGroup a :=
        MulAction.orbit_eq_iff.mpr hb
      rw [←he]
      exact codeCoupleOrbit_subset_coupleFusionOrbit b (hT.symm ▸ hc)

private theorem coupleFusion_t_mem (c : MinimalCross) :
    localFusionT • c∈MulAction.orbit coupleFusionGroup c :=
  MulAction.mem_orbit_iff.mpr ⟨⟨localFusionT,localFusionT_mem_coupleFusionGroup⟩,rfl⟩

 theorem coupleFusionTen_base_orbit :
    MulAction.orbit coupleFusionGroup localThirdCross=coupleFusionTen := by
  apply coupleFusion_orbit_union coupleCoordinateTwo coupleCoordinateEight coupleFusionTen
    localThirdCross (localFusionT • localThirdCross)
    (coupleCoordinateTwo_orbit _ localThirdCross_mem_coupleCoordinateTwo)
    (coupleCoordinateEight_orbit _ localFusionT_third_mem_coupleCoordinateEight)
    coupleFusionTen_decomposition (coupleFusion_t_mem _)
  exact coupleFusionTen_stable

 theorem coupleFusionEighty_base_orbit :
    MulAction.orbit coupleFusionGroup (coordinateCross localOutsideCoordinate)=coupleFusionEighty := by
  apply coupleFusion_orbit_union coupleCoordinateSixteen (coupleFourEnergyPiece 0) coupleFusionEighty
    (coordinateCross localOutsideCoordinate) localFourBridgeCross
    (coupleCoordinateSixteen_orbit _ localOutsideCoordinate_mem_coupleCoordinateSixteen)
    (coupleFourEnergyPiece_orbit 0 _ ⟨localFourBridgeCross_common,localFourBridgeCross_energy,localFourBridgeCross_four⟩)
    coupleFusionEighty_decomposition (coupleFusion_t_mem _)
  exact coupleFusionEighty_stable

 theorem coupleFusionSixForty_base_orbit :
    MulAction.orbit coupleFusionGroup shiftedSeedCross=coupleFusionSixForty := by
  have hH : MulAction.orbit codeCoupleStabilizer localHeavyBridgeCross=heavyCoupleNeighbours := by
    obtain ⟨w,hw⟩ := localHeavyBridgeCross_heavy
    rw [←hw]
    exact heavyCross_couple_stabilizer_orbit w (hw.symm ▸ localHeavyBridgeCross_common)
  apply coupleFusion_orbit_union (coupleFourEnergyPiece 2) heavyCoupleNeighbours coupleFusionSixForty
    shiftedSeedCross localHeavyBridgeCross
    (coupleFourEnergyPiece_orbit 2 _ ⟨shiftedSeedCross_common,shiftedSeedCross_energy,shiftedSeedCross_four⟩)
    hH coupleFusionSixForty_decomposition (coupleFusion_t_mem _)
  exact coupleFusionSixForty_stable

private theorem orbit_eq_from_base (S : Set MinimalCross) (a c : MinimalCross)
    (ha : MulAction.orbit coupleFusionGroup a=S) (hc : c∈S) :
    MulAction.orbit coupleFusionGroup c=S :=
  (MulAction.orbit_eq_iff.mpr (ha.symm ▸ hc)).trans ha

 theorem coupleFusionTen_orbit (c : MinimalCross) (hc : c∈coupleFusionTen) :
    MulAction.orbit coupleFusionGroup c=coupleFusionTen :=
  orbit_eq_from_base _ _ c coupleFusionTen_base_orbit hc

 theorem coupleFusionEighty_orbit (c : MinimalCross) (hc : c∈coupleFusionEighty) :
    MulAction.orbit coupleFusionGroup c=coupleFusionEighty :=
  orbit_eq_from_base _ _ c coupleFusionEighty_base_orbit hc

 theorem coupleFusionSixForty_orbit (c : MinimalCross) (hc : c∈coupleFusionSixForty) :
    MulAction.orbit coupleFusionGroup c=coupleFusionSixForty :=
  orbit_eq_from_base _ _ c coupleFusionSixForty_base_orbit hc

 theorem coupleFusionThousand_orbit (c : MinimalCross) (hc : c∈coupleFusionThousand) :
    MulAction.orbit coupleFusionGroup c=coupleFusionThousand := by
  have hH : MulAction.orbit codeCoupleStabilizer c=coupleFusionThousand := by
    rw [coupleFusionThousand_decomposition] at hc ⊢
    obtain ⟨w,hw⟩ := hc.2
    rw [←hw]
    exact heavyCross_semi_couple_stabilizer_orbit w (hw.symm ▸ hc.1)
  ext d
  constructor
  · intro hd
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hd
    exact coupleFusionThousand_stable g c hc
  · intro hd
    exact codeCoupleOrbit_subset_coupleFusionOrbit c (hH.symm ▸ hd)

 theorem coupleFusion_referenceSecond_orbit :
    MulAction.orbit coupleFusionGroup referenceSecondCross={referenceSecondCross} := by
  ext c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    exact (coupleFusionGroup_fix g).2
  · rintro rfl
    exact MulAction.mem_orbit_self _

 theorem coupleFusion_nontrivial_orbit_cards :
    (∀c∈coupleFusionTen,Nat.card (MulAction.orbit coupleFusionGroup c)=10) ∧
    (∀c∈coupleFusionEighty,Nat.card (MulAction.orbit coupleFusionGroup c)=80) ∧
    (∀c∈coupleFusionSixForty,Nat.card (MulAction.orbit coupleFusionGroup c)=640) ∧
    (∀c∈coupleFusionThousand,Nat.card (MulAction.orbit coupleFusionGroup c)=1024) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro c hc; rw [coupleFusionTen_orbit c hc,coupleFusionTen_card]
  · intro c hc; rw [coupleFusionEighty_orbit c hc,coupleFusionEighty_card]
  · intro c hc; rw [coupleFusionSixForty_orbit c hc,coupleFusionSixForty_card]
  · intro c hc; rw [coupleFusionThousand_orbit c hc,coupleFusionThousand_card]



/-- Exhaustion of the 1755 neighbours of the first cross by the five actual A-orbits. -/
theorem coupleFusion_neighbour_partition (c : MinimalCross)
    (hc : CrossOrthogonal localReferenceCross c) :
    c=referenceSecondCross ∨ c∈coupleFusionTen ∨ c∈coupleFusionEighty ∨
      c∈coupleFusionSixForty ∨ c∈coupleFusionThousand := by
  classical
  by_cases he : c=referenceSecondCross
  · exact Or.inl he
  by_cases hy : CrossOrthogonal referenceSecondCross c
  · have hcommon : ReferenceCoupleOrthogonal c := ⟨hc,hy⟩
    rcases reference_common_energy_cases c hcommon with h4|h0|h2
    · exact Or.inr (Or.inl ((coupleFusionTen_energy c).mpr ⟨hcommon,h4⟩))
    · exact Or.inr (Or.inr (Or.inl ((coupleFusionEighty_energy c).mpr ⟨hcommon,h0⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((coupleFusionSixForty_energy c).mpr ⟨hcommon,h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨hc,hy⟩,he⟩)))

 theorem coupleFusion_referenceSecond_orbit_card :
    Nat.card (MulAction.orbit coupleFusionGroup referenceSecondCross)=1 := by
  rw [coupleFusion_referenceSecond_orbit]
  simp

 theorem coupleFusion_neighbour_orbit_sizes (c : MinimalCross)
    (hc : CrossOrthogonal localReferenceCross c) :
    Nat.card (MulAction.orbit coupleFusionGroup c)=1 ∨
    Nat.card (MulAction.orbit coupleFusionGroup c)=10 ∨
    Nat.card (MulAction.orbit coupleFusionGroup c)=80 ∨
    Nat.card (MulAction.orbit coupleFusionGroup c)=640 ∨
    Nat.card (MulAction.orbit coupleFusionGroup c)=1024 := by
  rcases coupleFusion_neighbour_partition c hc with rfl|h|h|h|h
  · exact Or.inl coupleFusion_referenceSecond_orbit_card
  · exact Or.inr (Or.inl (coupleFusion_nontrivial_orbit_cards.1 c h))
  · exact Or.inr (Or.inr (Or.inl (coupleFusion_nontrivial_orbit_cards.2.1 c h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (coupleFusion_nontrivial_orbit_cards.2.2.1 c h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (coupleFusion_nontrivial_orbit_cards.2.2.2 c h))))

end Atlas.Rudvalis
