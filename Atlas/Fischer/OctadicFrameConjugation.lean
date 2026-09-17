import Atlas.Fischer.OctadicBasicFrameSwitch
import Atlas.Fischer.OctadicParityFrameMaximality

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Literal conjugation by the actual octadic root involution fixes its eight basics. -/
theorem octadicRoot_conjugation_inside (O : Octad) (χ : OctadicCharacter O)
    (i : Omega) (hi : i ∈ O.val) :
    (MulAut.conj (distinguishedRootElement (.inr (.inl ⟨O,χ⟩))))
      (distinguishedRootElement (.inl i))=distinguishedRootElement (.inl i) := by
  apply distinguishedRootElement_conjugation
  apply Subtype.ext
  change (displayedRootRayInvolution (.inr (.inl ⟨O,χ⟩)) (displayedRayOfParameter (.inl i))).val=_
  rw [displayedRootRayInvolution_parameter_value]
  change rootRay (rootMap (octadicRoot (chosenOctadCalibration O) χ) (basicAxis i))=_
  rw [octadicRoot_switch_inside _ _ _ hi]
  rfl

/-- Literal conjugation sends each exterior basic to its character-evaluation translate. -/
theorem octadicRoot_conjugation_outside (O : Octad) (χ : OctadicCharacter O)
    (i : OctadExterior O) :
    (MulAut.conj (distinguishedRootElement (.inr (.inl ⟨O,χ⟩))))
      (distinguishedRootElement (.inl i.val))=
        distinguishedRootElement (.inr (.inl ⟨O,χ+octadEvaluation O i⟩)) := by
  apply distinguishedRootElement_conjugation
  apply Subtype.ext
  change (displayedRootRayInvolution (.inr (.inl ⟨O,χ⟩)) (displayedRayOfParameter (.inl i.val))).val=_
  rw [displayedRootRayInvolution_parameter_value]
  change rootRay (rootMap (octadicRoot (chosenOctadCalibration O) χ) (basicAxis i.val))=_
  rw [octadicRoot_switch_outside]
  rfl

/-- The actual octadic switch carries the standard frame onto the opposite
character-parity frame. This is an equality of sets in the generated ray group. -/
theorem octadicRoot_conjugation_frame (O : Octad) (χ : OctadicCharacter O) :
    (MulAut.conj (distinguishedRootElement (.inr (.inl ⟨O,χ⟩)))) '' standardCommutingFrame=
      octadicParityFrame O (χ (octadShortenedOne O)+1) := by
  classical
  apply Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro x ⟨y,⟨i,rfl⟩,rfl⟩
    by_cases hi : i ∈ O.val
    · rw [octadicRoot_conjugation_inside O χ i hi]
      exact (mem_octadicParityFrame_basic _ _ _).mpr hi
    · rw [octadicRoot_conjugation_outside O χ (⟨i,hi⟩ : OctadExterior O)]
      apply (mem_octadicParityFrame_octadic _ _ _).mpr
      change χ (octadShortenedOne O)+octadEvaluation O ⟨i,hi⟩ (octadShortenedOne O)=_
      rw [octadEvaluation_one]
  · change Nat.card (octadicParityFrame O _ ) ≤ Nat.card _
    rw [octadicParityFrame_card,
      ← Nat.card_congr (Equiv.Set.image (MulAut.conj
        (distinguishedRootElement (.inr (.inl ⟨O,χ⟩)))) standardCommutingFrame
        (MulAut.conj _).injective),standardCommutingFrame_card]

end Atlas.Fischer
