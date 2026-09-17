import Atlas.Fischer.CoordinateSpace
import Atlas.Fischer.ParkerGolayFactorSet

namespace Atlas.Fischer
open Atlas.Codes

/-- The unique retained Golay word with the given octad support. -/
noncomputable def octadWord (O : Octad) : golay :=
  Classical.choose ((octads_mem O.val).mp O.prop)

theorem octadWord_weight (O : Octad) : hammingNorm (octadWord O : BinaryWord) = 8 :=
  (Classical.choose_spec ((octads_mem O.val).mp O.prop)).1

theorem octadWord_support (O : Octad) : support (octadWord O : BinaryWord) = O.val :=
  (Classical.choose_spec ((octads_mem O.val).mp O.prop)).2

abbrev SignedOctad := {d : ParkerLoop // hammingNorm (d.1 : BinaryWord) = 8}

noncomputable def signedOctadSupport (d : SignedOctad) : Octad :=
  ⟨support (d.val.1 : BinaryWord), (octads_mem _).mpr ⟨d.val.1, d.prop, rfl⟩⟩

noncomputable def canonicalOctadLift (O : Octad) : SignedOctad :=
  ⟨(octadWord O, 0), octadWord_weight O⟩

/-- No alternative code or sign section is hidden in the coordinate implementation. -/
noncomputable def signedOctadEquiv : SignedOctad ≃ Octad × ParkerBit where
  toFun d := (signedOctadSupport d, d.val.2)
  invFun p := ⟨(octadWord p.1, p.2), octadWord_weight p.1⟩
  left_inv d := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply support_injective
      exact octadWord_support (signedOctadSupport d)
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact octadWord_support p.1
    · rfl

def parkerScalarSign (b : ParkerBit) : Scalar := if b = 0 then 1 else -1

theorem parkerScalarSign_add (a b : ParkerBit) :
    parkerScalarSign (a + b) = parkerScalarSign a * parkerScalarSign b := by
  revert a b
  decide +kernel

theorem parkerScalarSign_one_add (b : ParkerBit) :
    parkerScalarSign (1 + b) = -parkerScalarSign b := by
  rw [parkerScalarSign_add]
  change (-1 : Scalar) * parkerScalarSign b = -parkerScalarSign b
  exact neg_one_mul _

noncomputable def signedOctadNegate (d : SignedOctad) : SignedOctad :=
  ⟨(d.val.1, 1 + d.val.2), d.prop⟩

/-- The source generator x_d, realized in the actual octad coordinate line. -/
noncomputable def signedOctadVector (d : SignedOctad) : Coordinates :=
  parkerScalarSign d.val.2 • xOctad (signedOctadSupport d)

theorem signedOctadVector_negate (d : SignedOctad) :
    signedOctadVector (signedOctadNegate d) = -signedOctadVector d := by
  simp only [signedOctadVector, signedOctadNegate, parkerScalarSign_one_add,
    neg_smul]
  rfl

theorem signedOctadVector_canonical (O : Octad) :
    signedOctadVector (canonicalOctadLift O) = xOctad O := by
  have h : signedOctadSupport (canonicalOctadLift O) = O := by
    apply Subtype.ext
    exact octadWord_support O
  change parkerScalarSign 0 • xOctad (signedOctadSupport (canonicalOctadLift O)) = _
  rw [h]
  simp [parkerScalarSign]

theorem signedOctadVector_norm (d : SignedOctad) :
    hermitian (signedOctadVector d) (signedOctadVector d) = 1 := by
  rw [signedOctadVector, hermitian_smul_left, hermitian_smul_right,
    hermitian_xOctad]
  simp only [ite_true]
  unfold parkerScalarSign
  split_ifs <;> norm_num

theorem signedOctad_cases (d : SignedOctad) :
    d = canonicalOctadLift (signedOctadSupport d) ∨
      d = signedOctadNegate (canonicalOctadLift (signedOctadSupport d)) := by
  have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
  have hc : d.val.1 = octadWord (signedOctadSupport d) := by
    apply Subtype.ext
    apply support_injective
    exact (octadWord_support (signedOctadSupport d)).symm
  rcases hb d.val.2 with h | h
  · left
    apply Subtype.ext
    exact Prod.ext hc h
  · right
    apply Subtype.ext
    apply Prod.ext hc
    simpa [signedOctadNegate, canonicalOctadLift] using h

/-- Any assignments respecting the signed-generator relation are determined by the
chosen 759 octad generators. This is the uniqueness part of the presentation. -/
theorem signedOctadAssignment_ext {M : Type*} [AddGroup M]
    (f g : SignedOctad → M)
    (hf : ∀ d, f (signedOctadNegate d) = -f d)
    (hg : ∀ d, g (signedOctadNegate d) = -g d)
    (h : ∀ O, f (canonicalOctadLift O) = g (canonicalOctadLift O)) : f = g := by
  funext d
  rcases signedOctad_cases d with hd | hd
  · rw [hd, h]
  · rw [hd, hf, hg, h]

end Atlas.Fischer
