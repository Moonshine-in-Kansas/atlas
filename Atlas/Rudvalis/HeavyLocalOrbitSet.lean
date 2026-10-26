import Atlas.Rudvalis.HeavyCoordinateStabilizerOrbit

/-! The heavy local orbit is exactly the 1536 orthogonal heavy crosses. -/
namespace Atlas.Rudvalis

def heavyCoordinateNeighbours (p : Point) : Set MinimalCross :=
  {c | CrossOrthogonal (coordinateCross (p,0)) c ∧
    ∃w : HeavyCrosses,shellPieceCrossMap heavyShellPiece w=c}

theorem shellPieceCross_range_stable (s : SubMulAction codeGroup MinimalShell)
    (g : codeGroup) (c : MinimalCross) (hc : ∃w : ShellPieceCross s,shellPieceCrossMap s w=c) :
    ∃w : ShellPieceCross s,shellPieceCrossMap s w=g • c := by
  obtain ⟨w,rfl⟩ := hc
  induction w using Quotient.inductionOn with
  | h v => exact ⟨Quotient.mk _ (g • v),rfl⟩

theorem crossOrthogonal_codeGroup (g : codeGroup) (a b : MinimalCross) :
    CrossOrthogonal (g • a) (g • b) ↔ CrossOrthogonal a b := by
  simpa only [codeGaussianHom_cross] using crossOrthogonal_gaussian (codeGaussianHom g) a b

noncomputable def heavyCoordinateNeighboursEquiv (p : Point) :
    {c : HeavyCrosses // CrossOrthogonal (coordinateCross (p,0)) (shellPieceCrossMap heavyShellPiece c)} ≃
      heavyCoordinateNeighbours p :=
  Equiv.ofBijective (fun c => ⟨shellPieceCrossMap heavyShellPiece c.val,c.prop,c.val,rfl⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (shellPieceCrossMap_injective _ (congrArg Subtype.val h))
    · rintro ⟨c,hc,⟨w,rfl⟩⟩
      exact ⟨⟨w,hc⟩,rfl⟩)

theorem heavyCoordinateNeighbours_card (p : Point) : Nat.card (heavyCoordinateNeighbours p)=1536 := by
  rw [←Nat.card_congr (heavyCoordinateNeighboursEquiv p)]
  exact heavyOrthogonalCrosses_card p 0

/-- Equality with the actual stabilizer orbit, including preservation of the heavy stratum. -/
theorem heavyCross_coordinate_stabilizer_orbit (p : Point) (w : HeavyCrosses)
    (hw : CrossOrthogonal (coordinateCross (p,0)) (shellPieceCrossMap heavyShellPiece w)) :
    MulAction.orbit (MulAction.stabilizer codeGroup (coordinateCross (p,0)))
      (shellPieceCrossMap heavyShellPiece w)=heavyCoordinateNeighbours p := by
  apply Set.ext
  intro c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    constructor
    · have h := (crossOrthogonal_codeGroup g.val _ _).mpr hw
      have hg : g.val • coordinateCross (p,0)=coordinateCross (p,0) := g.prop
      rw [hg] at h
      exact h
    · exact shellPieceCross_range_stable heavyShellPiece g.val _ ⟨w,rfl⟩
  · rintro ⟨hc,⟨v,rfl⟩⟩
    obtain ⟨g,hg,hgv⟩ := heavyCross_coordinate_stabilizer_transitive p w v hw hc
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g,hg⟩,hgv⟩

theorem heavyCross_coordinate_stabilizer_orbit_card (p : Point) (w : HeavyCrosses)
    (hw : CrossOrthogonal (coordinateCross (p,0)) (shellPieceCrossMap heavyShellPiece w)) :
    Nat.card (MulAction.orbit (MulAction.stabilizer codeGroup (coordinateCross (p,0)))
      (shellPieceCrossMap heavyShellPiece w))=1536 := by
  rw [heavyCross_coordinate_stabilizer_orbit p w hw,heavyCoordinateNeighbours_card]

end Atlas.Rudvalis
