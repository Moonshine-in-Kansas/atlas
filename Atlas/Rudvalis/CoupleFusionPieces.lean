import Atlas.Rudvalis.ReferenceQuartetExhaustion
import Atlas.Rudvalis.CoupleCoordinateOrbitSets
import Atlas.Rudvalis.CoupleFourOrbitSets
import Atlas.Rudvalis.HeavyCoupleComplementOrbit
import Atlas.Rudvalis.ProjectionOrthogonality

namespace Atlas.Rudvalis
open Classical

def coupleFusionTen : Set MinimalCross :=
  (referenceCoordinateDozen\{localReferenceCross})\{referenceSecondCross}
def coupleFusionEighty : Set MinimalCross :=
  {c | ∀z∈referenceCoordinateDozen,CrossOrthogonal z c}
def coupleFusionSixForty : Set MinimalCross :=
  {c | ReferenceCoupleOrthogonal c ∧ c∉referenceCoordinateDozen ∧ c∉coupleFusionEighty}
def coupleFusionThousand : Set MinimalCross :=
  {c | ReferenceCoupleSemiOrthogonal c ∧ c≠referenceSecondCross}

theorem coupleFusionTen_energy (c : MinimalCross) :
    c∈coupleFusionTen ↔ ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=4 := by
  constructor
  · intro hc
    exact (reference_coordinate_energy_four_iff ⟨c,referenceCoordinateDozen_subset hc.1.1⟩).mpr hc
  · intro hc
    rcases minimalCross_piece_cases c with ⟨a,ha⟩|⟨a,ha⟩|⟨a,ha⟩
    · exact (reference_coordinate_energy_four_iff ⟨c,ha ▸ ⟨a,rfl⟩⟩).mp hc
    · rw [←ha] at hc
      rcases fourCouple_energy_cases a hc.1 with he|he <;> rw [he] at hc <;> norm_num at hc
    · rw [←ha,heavyCouple_cross_energy a (ha.symm ▸ hc.1)] at hc
      norm_num at hc

theorem coupleFusionEighty_energy (c : MinimalCross) :
    c∈coupleFusionEighty ↔ ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=0 := by
  rw [crossRowEnergy_zero_iff]
  constructor
  · intro h; exact ⟨⟨h _ referenceCross_mem_dozen,h _ referenceSecondCross_mem_dozen⟩,h⟩
  · exact And.right

theorem coupleFusionSixForty_energy (c : MinimalCross) :
    c∈coupleFusionSixForty ↔ ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=2 := by
  constructor
  · rintro ⟨hc,hd,he⟩
    refine ⟨hc,?_⟩
    rcases reference_common_energy_cases c hc with h4|h0|h2
    · exact False.elim (hd ((coupleFusionTen_energy c).mpr ⟨hc,h4⟩).1.1)
    · exact False.elim (he ((coupleFusionEighty_energy c).mpr ⟨hc,h0⟩))
    · exact h2
  · rintro ⟨hc,he⟩
    refine ⟨hc,?_,?_⟩
    · intro hd
      have ht : c∈coupleFusionTen := ⟨⟨hd,fun h=>crossOrthogonal_irrefl _ (h ▸ hc.1)⟩,
        fun h=>crossOrthogonal_irrefl _ (h ▸ hc.2)⟩
      have hh := ((coupleFusionTen_energy c).mp ht).2
      rw [he] at hh; norm_num at hh
    · intro hz
      have hh := ((coupleFusionEighty_energy c).mp hz).2
      rw [he] at hh; norm_num at hh

theorem coupleFusionTen_card : Nat.card coupleFusionTen=10 := referenceCoordinateDozen_complement_pair_card
theorem coupleFusionEighty_card : Nat.card coupleFusionEighty=80 := reference_dozen_perpendicular_card
theorem coupleFusionSixForty_card : Nat.card coupleFusionSixForty=640 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight coupleFusionSixForty_energy)]
  exact reference_common_energy_counts.2.2

theorem coupleFusionEighty_decomposition :
    coupleFusionEighty=coupleCoordinateSixteen∪coupleFourEnergyPiece 0 := by
  ext c
  rw [coupleFusionEighty_energy]
  constructor
  · intro hc
    rcases minimalCross_piece_cases c with ⟨a,ha⟩|⟨a,ha⟩|⟨a,ha⟩
    · have hf : c∈coordinateFrame := ha ▸ ⟨a,rfl⟩
      exact Or.inl ⟨hf,(reference_coordinate_energy_zero_iff ⟨c,hf⟩).mp hc⟩
    · exact Or.inr ⟨hc.1,hc.2,a,ha⟩
    · have h := heavyCouple_cross_energy a (ha.symm ▸ hc.1)
      rw [ha,hc.2] at h; norm_num at h
  · rintro (hc|hc)
    · exact (reference_coordinate_energy_zero_iff ⟨c,hc.1⟩).mpr hc.2
    · exact ⟨hc.1,hc.2.1⟩

theorem coupleFusionSixForty_decomposition :
    coupleFusionSixForty=coupleFourEnergyPiece 2∪heavyCoupleNeighbours := by
  ext c
  rw [coupleFusionSixForty_energy]
  constructor
  · intro hc
    rcases minimalCross_piece_cases c with ⟨a,ha⟩|⟨a,ha⟩|⟨a,ha⟩
    · have h := coordinateFrame_energy referenceDozenRows ⟨c,ha ▸ ⟨a,rfl⟩⟩
      rw [hc.2] at h
      split_ifs at h <;> norm_num at h
    · exact Or.inl ⟨hc.1,hc.2,a,ha⟩
    · exact Or.inr ⟨hc.1,a,ha⟩
  · rintro (hc|⟨hc,a,rfl⟩)
    · exact ⟨hc.1,hc.2.1⟩
    · exact ⟨hc,heavyCouple_cross_energy a hc⟩



theorem coupleFusionTen_decomposition : coupleFusionTen=coupleCoordinateTwo∪coupleCoordinateEight := by
  ext c
  have hx : c=localReferenceCross → c∈coordinateRowFrame (rowLabel 0) := by
    rintro rfl; rw [localReferenceCross_eq]; exact ⟨0,rfl⟩
  have hy : c=referenceSecondCross → c∈coordinateRowFrame (rowLabel 0) := by
    rintro rfl; rw [referenceSecondCross_eq]; exact ⟨binaryLabel 2,rfl⟩
  have hs : c∈coordinateRowFrame (rowLabel 0) → c∈referenceCoordinateDozen := fun h=>coordinate_reference_row_subset_dozen h
  simp only [coupleFusionTen,coupleCoordinateTwo,coupleCoordinateEight,Set.mem_sdiff,Set.mem_singleton_iff,Set.mem_union]
  tauto

theorem coupleFusionThousand_decomposition : coupleFusionThousand=heavySemiCoupleNeighbours := by
  ext c
  constructor
  · rintro ⟨hc,hn⟩
    refine ⟨hc,?_⟩
    rcases minimalCross_piece_cases c with ⟨a,ha⟩|⟨a,ha⟩|⟨a,ha⟩
    · have hf : c∈coordinateFrame := ha ▸ ⟨a,rfl⟩
      have he : ¬referenceSecondCross≠c := by
        simpa only [coordinateFrame_orthogonal_iff _ _ (coordinateCross_mem _) hf] using hc.2
      exact False.elim (hn (not_not.mp he).symm)
    · have h0 := hc.1
      have h2 := hc.2
      rw [←ha,localReferenceCross_eq] at h0
      rw [←ha,referenceSecondCross_eq] at h2
      exact False.elim (h2 ((fourCross_coordinate_orthogonal_same_row a (rowLabel 0) 0 (binaryLabel 2)).mp h0))
    · exact ⟨a,ha⟩
  · rintro ⟨hc,a,ha⟩
    refine ⟨hc,?_⟩
    intro he
    obtain ⟨b,hb⟩ := (show referenceSecondCross∈coordinateFrame from coordinateCross_mem _)
    exact coordinate_heavy_cross_disjoint b a (hb.trans (ha.trans he).symm)

theorem coupleFusionThousand_card : Nat.card coupleFusionThousand=1024 := by
  rw [coupleFusionThousand_decomposition,heavySemiCoupleNeighbours_card]

end Atlas.Rudvalis
