import Atlas.Rudvalis.CoupleFourTransitivity
import Atlas.Rudvalis.CoupleRowEnergy
import Atlas.Rudvalis.FourLocalOrbitSet

namespace Atlas.Rudvalis

def coupleFourEnergyPiece (k : ℚ) : Set MinimalCross :=
  {c | ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=k ∧
    ∃v : FourBlockCrosses,shellPieceCrossMap fourShellPiece v=c}

noncomputable def coupleFourEnergyPieceEquiv (k : ℚ) :
    {v : FourBlockCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece v) ∧
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece v)=k} ≃
      coupleFourEnergyPiece k :=
  Equiv.ofBijective (fun v=>⟨shellPieceCrossMap fourShellPiece v.val,v.prop.1,v.prop.2,v.val,rfl⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (shellPieceCrossMap_injective _ (congrArg Subtype.val h))
    · rintro ⟨c,hc,he,⟨v,rfl⟩⟩
      exact ⟨⟨v,hc,he⟩,rfl⟩)

 theorem coupleFourEnergyPiece_zero_card : Nat.card (coupleFourEnergyPiece 0)=64 := by
  rw [←Nat.card_congr (coupleFourEnergyPieceEquiv 0)]
  exact fourCouple_energy_zero_card

 theorem coupleFourEnergyPiece_two_card : Nat.card (coupleFourEnergyPiece 2)=128 := by
  rw [←Nat.card_congr (coupleFourEnergyPieceEquiv 2)]
  exact fourCouple_energy_two_card

 theorem codeCouple_reference_orthogonal (g : codeCoupleStabilizer) (c : MinimalCross)
    (hc : ReferenceCoupleOrthogonal c) : ReferenceCoupleOrthogonal (g.val • c) := by
  have hx := (crossOrthogonal_codeGroup g.val localReferenceCross c).mpr hc.1
  have hy := (crossOrthogonal_codeGroup g.val referenceSecondCross c).mpr hc.2
  have hgx : g.val • localReferenceCross=localReferenceCross := g.prop.1
  have hgy : g.val • referenceSecondCross=referenceSecondCross := g.prop.2
  rw [hgx] at hx
  rw [hgy] at hy
  exact ⟨hx,hy⟩

 theorem coupleFourEnergyPiece_stable (k : ℚ) (g : codeCoupleStabilizer)
    (c : MinimalCross) (hc : c∈coupleFourEnergyPiece k) :
    g.val • c∈coupleFourEnergyPiece k := by
  exact ⟨codeCouple_reference_orthogonal g c hc.1,
    (codeCouple_crossRowEnergy g c).trans hc.2.1,
    shellPieceCross_range_stable fourShellPiece g.val c hc.2.2⟩

/-- Exact actual pair-stabilizer orbit, including preservation of its energy boundary. -/
 theorem coupleFourEnergyPiece_orbit (k : ℚ) (c : MinimalCross) (hc : c∈coupleFourEnergyPiece k) :
    MulAction.orbit codeCoupleStabilizer c=coupleFourEnergyPiece k := by
  ext d
  constructor
  · intro hd
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hd
    exact coupleFourEnergyPiece_stable k g c hc
  · intro hd
    obtain ⟨v,hv⟩ := hc.2.2
    obtain ⟨w,hw⟩ := hd.2.2
    have hvc : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece v) := hv.symm ▸ hc.1
    have hwc : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece w) := hw.symm ▸ hd.1
    have he : crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece v)=
        crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece w) := by
      rw [hv,hw,hc.2.1,hd.2.1]
    obtain ⟨g,hgx,hgy,hg⟩ := fourCouple_crosses_transitive v w hvc hwc he
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g,hgx,hgy⟩,by change g • c=d; simpa only [hv,hw] using hg⟩

 theorem coupleFourEnergyPiece_zero_orbit_card (c : MinimalCross) (hc : c∈coupleFourEnergyPiece 0) :
    Nat.card (MulAction.orbit codeCoupleStabilizer c)=64 := by
  rw [coupleFourEnergyPiece_orbit 0 c hc,coupleFourEnergyPiece_zero_card]

 theorem coupleFourEnergyPiece_two_orbit_card (c : MinimalCross) (hc : c∈coupleFourEnergyPiece 2) :
    Nat.card (MulAction.orbit codeCoupleStabilizer c)=128 := by
  rw [coupleFourEnergyPiece_orbit 2 c hc,coupleFourEnergyPiece_two_card]

end Atlas.Rudvalis
