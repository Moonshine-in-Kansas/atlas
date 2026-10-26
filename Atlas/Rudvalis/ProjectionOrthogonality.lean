import Atlas.Rudvalis.CommonPerpendicularSpectrum

namespace Atlas.Rudvalis
open Classical

theorem coordinateRowEnergy_zero_iff (s : Set Point) (v : RationalSpace) :
    coordinateRowEnergy s v=0 ↔ ∀i : Coordinate,i.1∈s → v i=0 := by
  rw [coordinateRowEnergy,rationalDot_self_eq_zero]
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa only [coordinateRowProjection_apply,hi,↓reduceIte,Pi.zero_apply] using he
  · intro h
    ext i
    by_cases hi : i.1∈s
    · simp only [coordinateRowProjection_apply,hi,↓reduceIte,Pi.zero_apply,h i hi]
    · simp only [coordinateRowProjection_apply,hi,↓reduceIte,Pi.zero_apply]

theorem crossRowEnergy_zero_iff (s : Set Point) (c : MinimalCross) :
    crossRowEnergy s c=0 ↔ ∀z∈selectedCoordinateRows s,CrossOrthogonal z c := by
  induction c using Quotient.inductionOn with
  | h v =>
    change coordinateRowEnergy s v.val.val=0 ↔ ∀z∈selectedCoordinateRows s,CrossOrthogonal z (minimalCross v)
    rw [coordinateRowEnergy_zero_iff]
    constructor
    · intro h z hz
      obtain ⟨p,hp,x,rfl⟩ := hz
      change CrossOrthogonal (minimalCross (coordinateShellLift ((p,x),true))) (minimalCross v)
      rw [crossOrthogonal_mk]
      change HermitianOrthogonal (coordinateMinimum (p,x)) v.val.val
      exact (coordinate_hermitianOrthogonal_pair p x v.val.val).mpr ⟨h (p,x) hp,h (p,x+p.val) hp⟩
    · intro h i hi
      have he := h (coordinateCross i) ⟨i.1,hi,i.2,rfl⟩
      rw [coordinateCross,crossOrthogonal_mk] at he
      change HermitianOrthogonal (coordinateMinimum i) v.val.val at he
      exact ((coordinate_hermitianOrthogonal_pair i.1 i.2 v.val.val).mp he).1

/-- The80-element common part is exactly the shell perpendicular to the selected dozen. -/
theorem reference_dozen_perpendicular_card :
    Nat.card {c : MinimalCross // ∀z∈referenceCoordinateDozen,CrossOrthogonal z c}=80 := by
  have he (c : MinimalCross) :
      (ReferenceCoupleOrthogonal c ∧ crossRowEnergy referenceDozenRows c=0) ↔
        ∀z∈referenceCoordinateDozen,CrossOrthogonal z c := by
    rw [crossRowEnergy_zero_iff]
    constructor
    · exact And.right
    · intro h
      exact ⟨⟨h _ referenceCross_mem_dozen,h _ referenceSecondCross_mem_dozen⟩,h⟩
  rw [←Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact reference_common_energy_counts.2.1

end Atlas.Rudvalis
