import Atlas.Rudvalis.FourCoupleProjection
import Atlas.Rudvalis.HeavyCoupleProjection

namespace Atlas.Rudvalis
open Classical

theorem coordinateFrame_energy (s : Set Point) (c : coordinateFrame) :
    crossRowEnergy s c.val=if c.val∈selectedCoordinateRows s then 4 else 0 := by
  obtain ⟨i,hi⟩ := coordinateFrame_rep c.val c.prop
  rw [←hi,crossRowEnergy_coordinateCross,coordinateCross_mem_selectedRows_iff]

theorem reference_coordinate_energy_four_iff (c : coordinateFrame) :
    ReferenceCoupleOrthogonal c.val ∧ crossRowEnergy referenceDozenRows c.val=4 ↔
      c.val∈(referenceCoordinateDozen\{localReferenceCross})\{referenceSecondCross} := by
  have hx := coordinateCross_mem (localFusionSourceCoordinate 0)
  have hy := coordinateCross_mem (localFusionSourceCoordinate 1)
  rw [ReferenceCoupleOrthogonal,coordinateFrame_orthogonal_iff _ _ hx c.prop,
    coordinateFrame_orthogonal_iff _ _ hy c.prop,coordinateFrame_energy]
  change (_ ∧ _) ∧ (if c.val∈referenceCoordinateDozen then (4:ℚ) else 0)=4 ↔ _
  simp only [Set.mem_sdiff,Set.mem_singleton_iff]
  by_cases h : c.val∈referenceCoordinateDozen
  · simp only [h,ite_true,ne_eq,true_and,and_true]
    tauto
  · norm_num only [h,ite_false,and_false,false_and]

theorem reference_coordinate_energy_zero_iff (c : coordinateFrame) :
    ReferenceCoupleOrthogonal c.val ∧ crossRowEnergy referenceDozenRows c.val=0 ↔
      c.val∉referenceCoordinateDozen := by
  rw [coordinateFrame_energy]
  change _ ∧ (if c.val∈referenceCoordinateDozen then (4:ℚ) else 0)=0 ↔ _
  by_cases h : c.val∈referenceCoordinateDozen
  · simp [h]
  · have hcx : localReferenceCross≠c.val := fun he => h (he ▸ referenceCross_mem_dozen)
    have hcy : referenceSecondCross≠c.val := fun he => h (he ▸ referenceSecondCross_mem_dozen)
    have hc : ReferenceCoupleOrthogonal c.val :=
      ⟨(coordinateFrame_orthogonal_iff _ _ (coordinateCross_mem _) c.prop).mpr hcx,
       (coordinateFrame_orthogonal_iff _ _ (coordinateCross_mem _) c.prop).mpr hcy⟩
    simp [h,hc]

theorem reference_coordinate_energy_four_card :
    Nat.card {c : coordinateFrame // ReferenceCoupleOrthogonal c.val ∧
      crossRowEnergy referenceDozenRows c.val=4}=10 := by
  let e : {c : coordinateFrame // ReferenceCoupleOrthogonal c.val ∧
      crossRowEnergy referenceDozenRows c.val=4} ≃
      ↥((referenceCoordinateDozen\{localReferenceCross})\{referenceSecondCross}) :=
    { toFun := fun c => ⟨c.val.val,(reference_coordinate_energy_four_iff c.val).mp c.prop⟩
      invFun := fun c => ⟨⟨c.val,referenceCoordinateDozen_subset c.prop.1.1⟩,
        (reference_coordinate_energy_four_iff _).mpr c.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact referenceCoordinateDozen_complement_pair_card

theorem reference_coordinate_energy_zero_card :
    Nat.card {c : coordinateFrame // ReferenceCoupleOrthogonal c.val ∧
      crossRowEnergy referenceDozenRows c.val=0}=16 := by
  let e : {c : coordinateFrame // ReferenceCoupleOrthogonal c.val ∧
      crossRowEnergy referenceDozenRows c.val=0} ≃ ↥(coordinateFrame\referenceCoordinateDozen) :=
    { toFun := fun c => ⟨c.val.val,c.val.prop,(reference_coordinate_energy_zero_iff c.val).mp c.prop⟩
      invFun := fun c => ⟨⟨c.val,c.prop.1⟩,(reference_coordinate_energy_zero_iff _).mpr c.prop.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact referenceCoordinateDozen_outside_card

theorem heavyCouple_cross_energy (c : HeavyCrosses)
    (hc : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece c)) :
    crossRowEnergy referenceDozenRows (shellPieceCrossMap heavyShellPiece c)=2 := by
  induction c using Quotient.inductionOn with
  | h v => exact heavyCouple_shell_energy ⟨v,hc⟩

end Atlas.Rudvalis
