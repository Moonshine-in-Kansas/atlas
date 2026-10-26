import Atlas.Rudvalis.CoupleConfigurationTransport
import Atlas.Rudvalis.LocalBridgeCommonEnergy

namespace Atlas.Rudvalis

theorem reference_four_not_intrinsicDozen (v : FourBlockCrosses)
    (hv : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece v)) :
    shellPieceCrossMap fourShellPiece v∉intrinsicDozen referenceCouple := by
  rcases fourCouple_energy_cases v hv with he|he
  · obtain ⟨w,hw⟩ := localFourBridgeCross_four
    have hwc : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece w) :=
      hw ▸ localFourBridgeCross_common
    have hwe : crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece w)=0 := by
      rw [hw,localFourBridgeCross_energy]
    intro h
    have hh := (fourCouple_intrinsicDozen_iff v w hv hwc (he.trans hwe.symm)).mp h
    rw [hw] at hh
    exact localFourBridgeCross_no_quartet hh
  · obtain ⟨w,hw⟩ := shiftedSeedCross_four
    have hwc : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece w) :=
      hw ▸ shiftedSeedCross_common
    have hwe : crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece w)=2 := by
      rw [hw,shiftedSeedCross_energy]
    intro h
    have hh := (fourCouple_intrinsicDozen_iff v w hv hwc (he.trans hwe.symm)).mp h
    rw [hw] at hh
    exact shiftedSeedCross_no_quartet hh

theorem reference_heavy_not_intrinsicDozen (v : HeavyCrosses)
    (hv : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece v)) :
    shellPieceCrossMap heavyShellPiece v∉intrinsicDozen referenceCouple := by
  obtain ⟨w,hw⟩ := localHeavyBridgeCross_heavy
  have hwc : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece w) :=
    hw ▸ localHeavyBridgeCross_common
  intro h
  have hh := (heavyCouple_intrinsicDozen_iff v w hv hwc).mp h
  rw [hw] at hh
  exact localHeavyBridgeCross_no_quartet hh

/-- Full intrinsic exhaustion: no noncoordinate quartet completion occurs. -/
theorem reference_intrinsicDozen_eq :
    intrinsicDozen referenceCouple=referenceCoordinateDozen :=
  reference_intrinsicDozen_eq_of_piece_exclusion reference_four_not_intrinsicDozen
    reference_heavy_not_intrinsicDozen

theorem reference_quartets_card : Nat.card (QuartetsThrough referenceCouple)=5 :=
  reference_quartets_card_of_dozen_equality reference_intrinsicDozen_eq

/-- Every actual orthogonal couple lies in exactly five intrinsic quartets. -/
theorem quartetsThrough_couple_card (c : Set MinimalCross) (hc : IsCouple c) :
    Nat.card (QuartetsThrough c)=5 := by
  rw [quartetsThrough_card_transport c hc,reference_quartets_card]

/-- Every intrinsic dozen has twelve actual Gaussian crosses. -/
theorem intrinsicDozen_couple_card (c : Set MinimalCross) (hc : IsCouple c) :
    Nat.card (intrinsicDozen c)=12 := by
  rw [intrinsicDozen_card_transport c hc,reference_intrinsicDozen_eq,referenceCoordinateDozen_card]

theorem intrinsicDozen_couple_pairwise (c : Set MinimalCross) (hc : IsCouple c) :
    (intrinsicDozen c).Pairwise CrossOrthogonal := by
  obtain ⟨g,hg⟩ := generated_couple_transport c hc
  rw [←hg,←intrinsicDozen_gaussianImage,reference_intrinsicDozen_eq,gaussianImage_pairwise]
  exact referenceCoordinateDozen_pairwise

end Atlas.Rudvalis
