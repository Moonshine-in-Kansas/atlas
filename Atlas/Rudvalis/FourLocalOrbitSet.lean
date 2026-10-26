import Atlas.Rudvalis.FourLocalCrossOrbit
import Atlas.Rudvalis.HeavyLocalOrbitSet

/-! The four-block local orbit is exactly the 192 orthogonal four-block crosses. -/
namespace Atlas.Rudvalis

def fourCoordinateNeighbours (p : Point) : Set MinimalCross :=
  {c | CrossOrthogonal (coordinateCross (p,0)) c ∧
    ∃w : FourBlockCrosses,shellPieceCrossMap fourShellPiece w=c}

noncomputable def fourCoordinateNeighboursEquiv (p : Point) :
    {c : FourBlockCrosses // CrossOrthogonal (coordinateCross (p,0)) (shellPieceCrossMap fourShellPiece c)} ≃
      fourCoordinateNeighbours p :=
  Equiv.ofBijective (fun c => ⟨shellPieceCrossMap fourShellPiece c.val,c.prop,c.val,rfl⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (shellPieceCrossMap_injective _ (congrArg Subtype.val h))
    · rintro ⟨c,hc,⟨w,rfl⟩⟩
      exact ⟨⟨w,hc⟩,rfl⟩)

theorem fourCoordinateNeighbours_card (p : Point) : Nat.card (fourCoordinateNeighbours p)=192 := by
  rw [←Nat.card_congr (fourCoordinateNeighboursEquiv p)]
  exact fourOrthogonalCrosses_card p 0

/-- Equality with the actual reference-cross stabilizer orbit. -/
theorem fourCross_reference_stabilizer_orbit (w : FourBlockCrosses)
    (hw : CrossOrthogonal (coordinateCross (rowLabel 0,0)) (shellPieceCrossMap fourShellPiece w)) :
    MulAction.orbit (MulAction.stabilizer codeGroup (coordinateCross (rowLabel 0,0)))
      (shellPieceCrossMap fourShellPiece w)=fourCoordinateNeighbours (rowLabel 0) := by
  apply Set.ext
  intro c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    constructor
    · have h := (crossOrthogonal_codeGroup g.val _ _).mpr hw
      have hg : g.val • coordinateCross (rowLabel 0,0)=coordinateCross (rowLabel 0,0) := g.prop
      rw [hg] at h
      exact h
    · exact shellPieceCross_range_stable fourShellPiece g.val _ ⟨w,rfl⟩
  · rintro ⟨hc,⟨v,rfl⟩⟩
    obtain ⟨g,hg,hgv⟩ := fourLocal_crosses_transitive w v hw hc
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g,hg⟩,hgv⟩

theorem fourCross_reference_stabilizer_orbit_card (w : FourBlockCrosses)
    (hw : CrossOrthogonal (coordinateCross (rowLabel 0,0)) (shellPieceCrossMap fourShellPiece w)) :
    Nat.card (MulAction.orbit (MulAction.stabilizer codeGroup (coordinateCross (rowLabel 0,0)))
      (shellPieceCrossMap fourShellPiece w))=192 := by
  rw [fourCross_reference_stabilizer_orbit w hw,fourCoordinateNeighbours_card]

end Atlas.Rudvalis
