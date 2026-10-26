import Atlas.Rudvalis.CrossPieceCount
import Atlas.Rudvalis.HeavyOrthogonalCount

namespace Atlas.Rudvalis

abbrev OrthogonalCrosses (x : MinimalCross) := {y : MinimalCross // CrossOrthogonal x y}

theorem coordinateOrthogonalCrosses_card (p : Point) (x : E) :
    Nat.card {c : CoordinateCrosses //
      CrossOrthogonal (coordinateCross (p,x)) (shellPieceCrossMap coordinateShellPiece c)}=27 := by
  let e : CoordinateCrosses ≃ coordinateFrame :=
    Equiv.ofInjective _ (shellPieceCrossMap_injective coordinateShellPiece)
  have h := Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl)
    (p := fun c => CrossOrthogonal (coordinateCross (p,x)) (shellPieceCrossMap coordinateShellPiece c))
    (q := fun c => CrossOrthogonal (coordinateCross (p,x)) c.val))
  rw [h]
  exact coordinateFrame_orthogonal_card ⟨coordinateCross (p,x),coordinateCross_mem _⟩

theorem coordinate_orthogonal_crosses_card (p : Point) (x : E) :
    Nat.card (OrthogonalCrosses (coordinateCross (p,x)))=1755 := by
  change Nat.card {c : MinimalCross // CrossOrthogonal (coordinateCross (p,x)) c}=1755
  rw [crossPiece_condition_card,coordinateOrthogonalCrosses_card,
    fourOrthogonalCrosses_card,heavyOrthogonalCrosses_card]

theorem coordinateFrame_orthogonal_crosses_card (x : MinimalCross) (hx : x∈coordinateFrame) :
    Nat.card (OrthogonalCrosses x)=1755 := by
  obtain ⟨⟨p,z⟩,rfl⟩ := coordinateFrame_rep x hx
  exact coordinate_orthogonal_crosses_card p z

noncomputable def orthogonalCrossTransport (g : gaussianLatticeGroup) (x : MinimalCross) :
    OrthogonalCrosses x ≃ OrthogonalCrosses (g • x) :=
  Equiv.subtypeEquiv (MulAction.toPerm g) (fun y => (crossOrthogonal_gaussian g x y).symm)

theorem orthogonalCross_card_transport (g : gaussianLatticeGroup) (x : MinimalCross) :
    Nat.card (OrthogonalCrosses (g • x))=Nat.card (OrthogonalCrosses x) :=
  (Nat.card_congr (orthogonalCrossTransport g x)).symm

theorem orthogonalCross_card_coordinate_orbit (g : gaussianLatticeGroup) (p : Point) (x : E) :
    Nat.card (OrthogonalCrosses (g • coordinateCross (p,x)))=1755 := by
  rw [orthogonalCross_card_transport,coordinate_orthogonal_crosses_card]

end Atlas.Rudvalis

