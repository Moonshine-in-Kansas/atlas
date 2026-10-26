import Atlas.Rudvalis.ReferenceProjectionSpectrum
import Atlas.Rudvalis.CommonPerpendicularCount

namespace Atlas.Rudvalis
open Classical

theorem coordinatePiece_condition_card (P : MinimalCross→Prop) :
    Nat.card {c : CoordinateCrosses // P (shellPieceCrossMap coordinateShellPiece c)}=
      Nat.card {c : coordinateFrame // P c.val} := by
  let e : CoordinateCrosses ≃ coordinateFrame :=
    Equiv.ofInjective _ (shellPieceCrossMap_injective coordinateShellPiece)
  exact Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

theorem reference_coordinate_energy_two_card :
    Nat.card {c : coordinateFrame // ReferenceCoupleOrthogonal c.val ∧
      crossRowEnergy referenceDozenRows c.val=2}=0 := by
  let : IsEmpty {c : coordinateFrame // ReferenceCoupleOrthogonal c.val ∧
      crossRowEnergy referenceDozenRows c.val=2} := ⟨fun c => by
    have h := c.prop.2
    rw [coordinateFrame_energy] at h
    split_ifs at h <;> norm_num at h⟩
  exact Nat.card_of_isEmpty

theorem reference_four_energy_four_card :
    Nat.card {c : FourBlockCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece c) ∧
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece c)=4}=0 := by
  let : IsEmpty {c : FourBlockCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece c) ∧
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece c)=4} := ⟨fun c => by
    have h := c.prop.2
    rcases fourCouple_energy_cases c.val c.prop.1 with h0|h0 <;> rw [h0] at h <;> norm_num at h⟩
  exact Nat.card_of_isEmpty

theorem reference_heavy_energy_card (k : ℚ) :
    Nat.card {c : HeavyCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece c) ∧
      crossRowEnergy referenceDozenRows (shellPieceCrossMap heavyShellPiece c)=k}=
        if k=2 then 512 else 0 := by
  by_cases hk : k=2
  · subst k
    simp only [↓reduceIte]
    have he : Nat.card {c : HeavyCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece c) ∧
        crossRowEnergy referenceDozenRows (shellPieceCrossMap heavyShellPiece c)=2}=
        Nat.card {c : HeavyCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece c)} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (fun c => ⟨And.left,fun h=>⟨h,heavyCouple_cross_energy c h⟩⟩)
    rw [he]
    exact heavyCommonPerpendicularCrosses_card
  · rw [ite_eq_right_iff.mpr (fun h=>False.elim (hk h))]
    let : IsEmpty {c : HeavyCrosses // ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece c) ∧
        crossRowEnergy referenceDozenRows (shellPieceCrossMap heavyShellPiece c)=k} := ⟨fun c =>
      hk (c.prop.2.symm.trans (heavyCouple_cross_energy c.val c.prop.1))⟩
    exact Nat.card_of_isEmpty

/-- The selected-row projection decomposes the common perpendicular shell as10+80+640. -/
theorem reference_common_energy_counts :
    Nat.card {c : MinimalCross // ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=4}=10 ∧
    Nat.card {c : MinimalCross // ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=0}=80 ∧
    Nat.card {c : MinimalCross // ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=2}=640 := by
  constructor
  · rw [crossPiece_condition_card,coordinatePiece_condition_card (fun c=>ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=4),
      reference_coordinate_energy_four_card,reference_four_energy_four_card,reference_heavy_energy_card]
    norm_num
  constructor
  · rw [crossPiece_condition_card,coordinatePiece_condition_card (fun c=>ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=0),
      reference_coordinate_energy_zero_card,fourCouple_energy_zero_card,reference_heavy_energy_card]
    norm_num
  · rw [crossPiece_condition_card,coordinatePiece_condition_card (fun c=>ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=2),
      reference_coordinate_energy_two_card,fourCouple_energy_two_card,reference_heavy_energy_card]
    norm_num

theorem reference_common_energy_cases (c : MinimalCross) (hc : ReferenceCoupleOrthogonal c) :
    crossRowEnergy referenceDozenRows c=4 ∨ crossRowEnergy referenceDozenRows c=0 ∨
      crossRowEnergy referenceDozenRows c=2 := by
  rcases minimalCross_piece_cases c with ⟨a,ha⟩|⟨a,ha⟩|⟨a,ha⟩
  · have hm : c∈coordinateFrame := ha ▸ ⟨a,rfl⟩
    have h := coordinateFrame_energy referenceDozenRows ⟨c,hm⟩
    split_ifs at h with he
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [←ha] at hc ⊢
    exact Or.inr (fourCouple_energy_cases a hc)
  · rw [←ha] at hc ⊢
    exact Or.inr (Or.inr (heavyCouple_cross_energy a hc))

end Atlas.Rudvalis
