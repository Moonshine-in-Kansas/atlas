import Atlas.Rudvalis.HeavyCoupleComplement

namespace Atlas.Rudvalis

def heavySemiCoupleNeighbours : Set MinimalCross :=
  {c | ReferenceCoupleSemiOrthogonal c ∧ ∃w : HeavyCrosses,shellPieceCrossMap heavyShellPiece w=c}

theorem heavyCoupleNeighbours_subset_coordinateNeighbours :
    heavyCoupleNeighbours⊆heavyCoordinateNeighbours (rowLabel 0) := by
  rintro c ⟨hc,hw⟩
  exact ⟨localReferenceCross_eq ▸ hc.1,hw⟩

theorem heavySemiCoupleNeighbours_eq_difference :
    heavySemiCoupleNeighbours=heavyCoordinateNeighbours (rowLabel 0)\heavyCoupleNeighbours := by
  ext c
  simp only [heavySemiCoupleNeighbours,heavyCoordinateNeighbours,heavyCoupleNeighbours,
    ReferenceCoupleSemiOrthogonal,ReferenceCoupleOrthogonal,Set.mem_ofPred_eq,Set.mem_sdiff,
    localReferenceCross_eq]
  tauto

theorem heavySemiCoupleNeighbours_card : Nat.card heavySemiCoupleNeighbours=1024 := by
  rw [heavySemiCoupleNeighbours_eq_difference]
  change (heavyCoordinateNeighbours (rowLabel 0)\heavyCoupleNeighbours).ncard=1024
  rw [Set.ncard_sdiff heavyCoupleNeighbours_subset_coordinateNeighbours]
  change Nat.card (heavyCoordinateNeighbours (rowLabel 0))-Nat.card heavyCoupleNeighbours=1024
  rw [heavyCoordinateNeighbours_card,heavyCoupleNeighbours_card]

theorem heavyCross_semi_couple_stabilizer_orbit (w : HeavyCrosses)
    (hw : ReferenceCoupleSemiOrthogonal (shellPieceCrossMap heavyShellPiece w)) :
    MulAction.orbit codeCoupleStabilizer (shellPieceCrossMap heavyShellPiece w)=heavySemiCoupleNeighbours := by
  ext c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    constructor
    · have h0 := (crossOrthogonal_codeGroup g.val _ _).mpr hw.1
      have h2 := (crossOrthogonal_codeGroup g.val _ _).not.mpr hw.2
      rw [g.prop.1] at h0
      rw [g.prop.2] at h2
      exact ⟨h0,h2⟩
    · exact shellPieceCross_range_stable heavyShellPiece g.val _ ⟨w,rfl⟩
  · rintro ⟨hc,⟨v,rfl⟩⟩
    obtain ⟨g,hg⟩ := heavyCross_semi_couple_stabilizer_transitive w v hw hc
    exact MulAction.mem_orbit_iff.mpr ⟨g,hg⟩

theorem heavyCross_semi_couple_stabilizer_orbit_card (w : HeavyCrosses)
    (hw : ReferenceCoupleSemiOrthogonal (shellPieceCrossMap heavyShellPiece w)) :
    Nat.card (MulAction.orbit codeCoupleStabilizer (shellPieceCrossMap heavyShellPiece w))=1024 := by
  rw [heavyCross_semi_couple_stabilizer_orbit w hw,heavySemiCoupleNeighbours_card]

end Atlas.Rudvalis
