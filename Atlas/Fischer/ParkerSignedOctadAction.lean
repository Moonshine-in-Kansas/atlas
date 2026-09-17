import Atlas.Fischer.ParkerStandardParity
import Atlas.Fischer.SignedOctads

namespace Atlas.Fischer
open Atlas.Codes

noncomputable def parkerSignedOctadAction (e : ParkerStandardGroup) (d : SignedOctad) :
    SignedOctad := ⟨e.val d.val, by
  change hammingNorm ((e.val d.val).1 : BinaryWord) = 8
  rw [parkerStandardProjection_spec, parkerCodeEquiv_weight]
  exact d.property⟩

theorem parkerSignedOctadAction_one (d : SignedOctad) : parkerSignedOctadAction 1 d = d := by
  apply Subtype.ext
  rfl

theorem parkerSignedOctadAction_mul (e f : ParkerStandardGroup) (d : SignedOctad) :
    parkerSignedOctadAction (e * f) d =
      parkerSignedOctadAction e (parkerSignedOctadAction f d) := by
  apply Subtype.ext
  rfl

theorem parkerSignedOctadAction_negate (e : ParkerStandardGroup) (d : SignedOctad) :
    parkerSignedOctadAction e (signedOctadNegate d) =
      signedOctadNegate (parkerSignedOctadAction e d) := by
  apply Subtype.ext
  have h := parkerStandard_preserves_sign e 1 d.val
  simpa only [parkerSignedOctadAction, signedOctadNegate, parkerSign, add_comm] using h

noncomputable def parkerOctadAction (e : ParkerStandardGroup) (O : Octad) : Octad :=
  ⟨permuteBlock (parkerStandardProjection e).val O.val,
    codePreserving_octad_forward _ (parkerStandardProjection e).property O.val O.property⟩

theorem parkerOctadAction_one (O : Octad) : parkerOctadAction 1 O = O := by
  apply Subtype.ext
  simp [parkerOctadAction]

theorem parkerOctadAction_mul (e f : ParkerStandardGroup) (O : Octad) :
    parkerOctadAction (e * f) O = parkerOctadAction e (parkerOctadAction f O) := by
  apply Subtype.ext
  simp [parkerOctadAction, permuteBlock_mul]

theorem parkerSignedOctadAction_support (e : ParkerStandardGroup) (d : SignedOctad) :
    signedOctadSupport (parkerSignedOctadAction e d) =
      parkerOctadAction e (signedOctadSupport d) := by
  apply Subtype.ext
  change support ((e.val d.val).1 : BinaryWord) =
    permuteBlock (parkerStandardProjection e).val (support (d.val.1 : BinaryWord))
  rw [parkerStandardProjection_spec]
  exact coordinatePermutation_support _ _

noncomputable def parkerOctadEquiv (e : ParkerStandardGroup) : Equiv.Perm Octad where
  toFun := parkerOctadAction e
  invFun := parkerOctadAction e⁻¹
  left_inv O := by rw [← parkerOctadAction_mul, inv_mul_cancel, parkerOctadAction_one]
  right_inv O := by rw [← parkerOctadAction_mul, mul_inv_cancel, parkerOctadAction_one]

noncomputable def parkerCoordinateEquiv (e : ParkerStandardGroup) : Equiv.Perm CoordinateIndex :=
  Equiv.sumCongr (parkerStandardProjection e).val (parkerOctadEquiv e)

theorem parkerCoordinateEquiv_weight (e : ParkerStandardGroup) (i : CoordinateIndex) :
    coordinateWeight (parkerCoordinateEquiv e i) = coordinateWeight i := by
  cases i <;> rfl

end Atlas.Fischer
