import Atlas.Rudvalis.CoordinateCommonPerpendicular

namespace Atlas.Rudvalis

theorem fourCross_coordinate_orthogonal_same_row (c : FourBlockCrosses) (p : Point) (x y : E) :
    CrossOrthogonal (coordinateCross (p,x)) (shellPieceCrossMap fourShellPiece c) ↔
      CrossOrthogonal (coordinateCross (p,y)) (shellPieceCrossMap fourShellPiece c) := by
  induction c using Quotient.inductionOn with
  | h v =>
    obtain ⟨w,hw⟩ := v.prop
    change CrossOrthogonal (coordinateCross (p,x)) (minimalCross v.val) ↔
      CrossOrthogonal (coordinateCross (p,y)) (minimalCross v.val)
    rw [←hw]
    exact (fourWord_coordinate_orthogonal_iff w p x).trans (fourWord_coordinate_orthogonal_iff w p y).symm

theorem four_common_perpendicular_card :
    Nat.card {c : FourBlockCrosses //
      CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece c) ∧
      CrossOrthogonal referenceSecondCross (shellPieceCrossMap fourShellPiece c)}=192 := by
  rw [localReferenceCross_eq,referenceSecondCross_eq]
  have he (c : FourBlockCrosses) :
      (CrossOrthogonal (coordinateCross (rowLabel 0,0)) (shellPieceCrossMap fourShellPiece c) ∧
        CrossOrthogonal (coordinateCross (rowLabel 0,binaryLabel 2)) (shellPieceCrossMap fourShellPiece c)) ↔
      CrossOrthogonal (coordinateCross (rowLabel 0,0)) (shellPieceCrossMap fourShellPiece c) :=
    ⟨And.left,fun h => ⟨h,(fourCross_coordinate_orthogonal_same_row c _ _ _).mp h⟩⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact fourOrthogonalCrosses_card _ _

end Atlas.Rudvalis
