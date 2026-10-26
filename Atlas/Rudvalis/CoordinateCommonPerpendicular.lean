import Atlas.Rudvalis.LocalTransitivity
import Mathlib.Data.Set.Card

namespace Atlas.Rudvalis

noncomputable abbrev referenceSecondCross : MinimalCross :=
  coordinateCross (localFusionSourceCoordinate 1)

theorem referenceSecondCoordinate_eq : localFusionSourceCoordinate 1=(rowLabel 0,binaryLabel 2) := by
  decide +kernel

theorem referenceSecondCross_eq : referenceSecondCross=coordinateCross (rowLabel 0,binaryLabel 2) :=
  congrArg coordinateCross referenceSecondCoordinate_eq

abbrev CommonPerpendicularCrosses (x y : MinimalCross) :=
  {c : MinimalCross // CrossOrthogonal x c ∧ CrossOrthogonal y c}

theorem reference_crosses_ne : localReferenceCross≠referenceSecondCross := by
  intro h
  rcases (coordinateCross_eq_iff _ _).mp h with h|h
  · exact (by decide +kernel : localFusionSourceCoordinate 0≠localFusionSourceCoordinate 1) h
  · rw [codeI_coordinate,localReferenceCoordinate_eq,referenceSecondCoordinate_eq] at h
    exact (by decide +kernel : (rowLabel 0,(0:E)+(rowLabel 0).val)≠(rowLabel 0,binaryLabel 2)) h

theorem reference_crosses_orthogonal : CrossOrthogonal localReferenceCross referenceSecondCross :=
  (coordinateFrame_orthogonal_iff _ _ (coordinateCross_mem _) (coordinateCross_mem _)).mpr reference_crosses_ne

theorem coordinateFrame_common_orthogonal_card (x y : coordinateFrame) (hxy : x≠y) :
    Nat.card {c : coordinateFrame // CrossOrthogonal x.val c.val ∧ CrossOrthogonal y.val c.val}=26 := by
  classical
  have hxy' : x.val≠y.val := fun h => hxy (Subtype.ext h)
  let e : {c : coordinateFrame // CrossOrthogonal x.val c.val ∧ CrossOrthogonal y.val c.val} ≃
      ↥((coordinateFrame\{x.val})\{y.val}) :=
    { toFun := fun c => ⟨c.val.val,⟨c.val.prop,by
        intro he; exact crossOrthogonal_irrefl _ (he ▸ c.prop.1)⟩,by
        intro he; exact crossOrthogonal_irrefl _ (he ▸ c.prop.2)⟩
      invFun := fun c => ⟨⟨c.val,c.prop.1.1⟩,
        (coordinateFrame_orthogonal_iff _ _ x.prop c.prop.1.1).mpr (Ne.symm c.prop.1.2),
        (coordinateFrame_orthogonal_iff _ _ y.prop c.prop.1.1).mpr (Ne.symm c.prop.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  change ((coordinateFrame\{x.val})\{y.val}).ncard=26
  rw [Set.ncard_sdiff_singleton_of_mem (show y.val∈coordinateFrame\{x.val} from ⟨y.prop,Ne.symm hxy'⟩),
    Set.ncard_sdiff_singleton_of_mem x.prop]
  change Nat.card coordinateFrame-1-1=26
  rw [coordinateFrame_card]

theorem coordinate_common_perpendicular_card :
    Nat.card {c : CoordinateCrosses //
      CrossOrthogonal localReferenceCross (shellPieceCrossMap coordinateShellPiece c) ∧
      CrossOrthogonal referenceSecondCross (shellPieceCrossMap coordinateShellPiece c)}=26 := by
  let e : CoordinateCrosses ≃ coordinateFrame :=
    Equiv.ofInjective _ (shellPieceCrossMap_injective coordinateShellPiece)
  rw [Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl)
    (p := fun c => CrossOrthogonal localReferenceCross (shellPieceCrossMap coordinateShellPiece c) ∧
      CrossOrthogonal referenceSecondCross (shellPieceCrossMap coordinateShellPiece c))
    (q := fun c => CrossOrthogonal localReferenceCross c.val ∧ CrossOrthogonal referenceSecondCross c.val))]
  exact coordinateFrame_common_orthogonal_card
    ⟨localReferenceCross,coordinateCross_mem _⟩ ⟨referenceSecondCross,coordinateCross_mem _⟩
    (fun h => reference_crosses_ne (congrArg Subtype.val h))

end Atlas.Rudvalis
