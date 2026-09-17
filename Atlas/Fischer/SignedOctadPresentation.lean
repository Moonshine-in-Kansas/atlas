import Atlas.Fischer.SignedOctads

namespace Atlas.Fischer
open Atlas.Codes

noncomputable def signedOctadWVector (d : SignedOctad) : OctadCoordinates :=
  parkerScalarSign d.val.2 • (Pi.basisFun Scalar Octad) (signedOctadSupport d)

theorem signedOctadWVector_negate (d : SignedOctad) :
    signedOctadWVector (signedOctadNegate d) = -signedOctadWVector d := by
  simp only [signedOctadWVector, signedOctadNegate, parkerScalarSign_one_add, neg_smul]
  rfl

theorem signedOctadWVector_canonical (O : Octad) :
    signedOctadWVector (canonicalOctadLift O) = (Pi.basisFun Scalar Octad) O := by
  have h : signedOctadSupport (canonicalOctadLift O) = O := by
    apply Subtype.ext
    exact octadWord_support O
  change parkerScalarSign 0 • (Pi.basisFun Scalar Octad)
    (signedOctadSupport (canonicalOctadLift O)) = _
  rw [h]
  simp [parkerScalarSign]

/-- The universal property of the source's signed-generator presentation:
its sole linear relations are x_{−d}=−x_d. -/
theorem signedOctadPresentation {M : Type*} [AddCommGroup M] [Module Scalar M]
    (f : SignedOctad → M) (hf : ∀ d, f (signedOctadNegate d) = -f d) :
    ∃! L : OctadCoordinates →ₗ[Scalar] M, ∀ d, L (signedOctadWVector d) = f d := by
  classical
  let L : OctadCoordinates →ₗ[Scalar] M :=
    (Pi.basisFun Scalar Octad).constr Scalar (fun O => f (canonicalOctadLift O))
  have hc (O : Octad) : L (signedOctadWVector (canonicalOctadLift O)) =
      f (canonicalOctadLift O) := by
    rw [signedOctadWVector_canonical]
    exact (Pi.basisFun Scalar Octad).constr_basis Scalar _ O
  have ha : ∀ d, L (signedOctadWVector d) = f d := by
    intro d
    have h := signedOctadAssignment_ext (fun d => L (signedOctadWVector d)) f
      (fun d => by rw [signedOctadWVector_negate, map_neg]) hf hc
    exact congrFun h d
  refine ⟨L, ha, ?_⟩
  intro K hK
  apply (Pi.basisFun Scalar Octad).ext
  intro O
  have he := (hK (canonicalOctadLift O)).trans (hc O).symm
  simpa only [signedOctadWVector_canonical] using he

end Atlas.Fischer
