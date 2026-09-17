import Atlas.Fischer.ParkerSignedOctadAction

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerOctadWord_action (e : ParkerStandardGroup) (O : Octad) :
    parkerCodeEquiv (parkerStandardProjection e) (octadWord O) =
      octadWord (parkerOctadAction e O) := by
  apply Subtype.ext
  apply support_injective
  rw [parkerCodeEquiv_coe, coordinatePermutation_support, octadWord_support, octadWord_support]
  rfl

noncomputable def parkerCoordinateSign (e : ParkerStandardGroup) : CoordinateIndex → Bit
  | Sum.inl _ => 0
  | Sum.inr O => (e.val (canonicalOctadLift O).val).2

theorem parkerStandard_canonical_octad (e : ParkerStandardGroup) (O : Octad) :
    e.val (canonicalOctadLift O).val =
      parkerSign (parkerCoordinateSign e (.inr O)) (canonicalOctadLift (parkerOctadAction e O)).val := by
  apply Prod.ext
  · rw [parkerStandardProjection_spec]
    exact parkerOctadWord_action e O
  · change (e.val (canonicalOctadLift O).val).2 = 0 + (e.val (canonicalOctadLift O).val).2
    simp

theorem parkerCoordinateSign_one (i : CoordinateIndex) : parkerCoordinateSign 1 i = 0 := by
  cases i <;> rfl

theorem parkerCoordinateEquiv_one (i : CoordinateIndex) : parkerCoordinateEquiv 1 i = i := by
  cases i with
  | inl p =>
    change Sum.inl ((parkerStandardProjection 1).val p) = Sum.inl p
    rw [map_one]
    rfl
  | inr O => exact congrArg Sum.inr (parkerOctadAction_one O)

theorem parkerCoordinateEquiv_mul (e f : ParkerStandardGroup) (i : CoordinateIndex) :
    parkerCoordinateEquiv (e * f) i = parkerCoordinateEquiv e (parkerCoordinateEquiv f i) := by
  cases i with
  | inl p =>
    change Sum.inl ((parkerStandardProjection (e * f)).val p) = _
    rw [map_mul]
    rfl
  | inr O => exact congrArg Sum.inr (parkerOctadAction_mul e f O)

theorem parkerCoordinateSign_mul (e f : ParkerStandardGroup) (i : CoordinateIndex) :
    parkerCoordinateSign (e * f) i =
      parkerCoordinateSign e (parkerCoordinateEquiv f i) + parkerCoordinateSign f i := by
  cases i with
  | inl p => rfl
  | inr O =>
    change (e.val (f.val (canonicalOctadLift O).val)).2 =
      (e.val (canonicalOctadLift (parkerOctadAction f O)).val).2 +
        (f.val (canonicalOctadLift O).val).2
    rw [parkerStandard_canonical_octad f O, parkerStandard_preserves_sign]
    simp [parkerSign, parkerCoordinateSign, canonicalOctadLift]

end Atlas.Fischer
