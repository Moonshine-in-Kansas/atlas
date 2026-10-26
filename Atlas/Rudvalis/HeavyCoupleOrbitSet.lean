import Atlas.Rudvalis.HeavyCoupleTransitivity

namespace Atlas.Rudvalis

def heavyCoupleNeighbours : Set MinimalCross :=
  {c | ReferenceCoupleOrthogonal c ∧ ∃w : HeavyCrosses,shellPieceCrossMap heavyShellPiece w=c}

noncomputable def heavyCoupleNeighboursEquiv :
    {c : HeavyCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece c)} ≃
      heavyCoupleNeighbours :=
  Equiv.ofBijective (fun c => ⟨shellPieceCrossMap heavyShellPiece c.val,c.prop,c.val,rfl⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (shellPieceCrossMap_injective _ (congrArg Subtype.val h))
    · rintro ⟨c,hc,⟨w,rfl⟩⟩
      exact ⟨⟨w,hc⟩,rfl⟩)

theorem heavyCoupleNeighbours_card : Nat.card heavyCoupleNeighbours=512 := by
  rw [←Nat.card_congr heavyCoupleNeighboursEquiv]
  exact heavyCommonPerpendicularCrosses_card

theorem heavyCross_couple_stabilizer_orbit (w : HeavyCrosses)
    (hw : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece w)) :
    MulAction.orbit codeCoupleStabilizer (shellPieceCrossMap heavyShellPiece w)=heavyCoupleNeighbours := by
  ext c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    constructor
    · have h0 := (crossOrthogonal_codeGroup g.val _ _).mpr hw.1
      have h2 := (crossOrthogonal_codeGroup g.val _ _).mpr hw.2
      rw [g.prop.1] at h0
      rw [g.prop.2] at h2
      exact ⟨h0,h2⟩
    · exact shellPieceCross_range_stable heavyShellPiece g.val _ ⟨w,rfl⟩
  · rintro ⟨hc,⟨v,rfl⟩⟩
    obtain ⟨g,hg⟩ := heavyCross_couple_stabilizer_transitive w v hw hc
    exact MulAction.mem_orbit_iff.mpr ⟨g,hg⟩

theorem heavyCross_couple_stabilizer_orbit_card (w : HeavyCrosses)
    (hw : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece w)) :
    Nat.card (MulAction.orbit codeCoupleStabilizer (shellPieceCrossMap heavyShellPiece w))=512 := by
  rw [heavyCross_couple_stabilizer_orbit w hw,heavyCoupleNeighbours_card]

end Atlas.Rudvalis
