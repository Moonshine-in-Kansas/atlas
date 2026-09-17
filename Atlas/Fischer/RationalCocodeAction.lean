import Atlas.Fischer.RationalCocodeLabels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The rational coordinate change of a scalar under a signed conjugation. -/
theorem scalarRealThetaFunEquiv_signed (a b : Bit) (z : Scalar) (k : Fin 2) :
    scalarRealThetaFunEquiv (parkerScalarSign a * scalarParityAut b z) k =
      rationalBitSign (a + if k=0 then 0 else b) * scalarRealThetaFunEquiv z k := by
  have hb : ∀ t : Bit, t=0 ∨ t=1 := by decide
  rcases hb a with rfl | rfl <;> rcases hb b with rfl | rfl <;> fin_cases k <;>
    simp [parkerScalarSign,scalarParityAut_zero,scalarParityAut_one,
      rationalBitSign,scalarRealThetaFunEquiv,scalarRealThetaEquiv] <;> ring

theorem parkerCoordinateEquiv_cocode (d : Cocode) :
    parkerCoordinateEquiv (parkerCocodeStandard d)=1 := by
  apply Equiv.ext
  intro i
  cases i with
  | inl i =>
    change Sum.inl ((parkerStandardProjection (parkerCocodeStandard d)).val i)=Sum.inl i
    rw [parkerCocodeStandard_projection]
    rfl
  | inr O =>
    apply congrArg Sum.inr
    apply Subtype.ext
    change permuteBlock (parkerStandardProjection (parkerCocodeStandard d)).val O.val=O.val
    rw [parkerCocodeStandard_projection]
    exact permuteBlock_one O.val

theorem parkerCoordinateSign_cocode (d : Cocode) (i : CoordinateIndex) :
    parkerCoordinateSign (parkerCocodeStandard d) i =
      cocodePairing (match i with | Sum.inl _ => 0 | Sum.inr O => octadWord O) d := by
  cases i <;> simp [parkerCoordinateSign,parkerCocodeStandard_apply,canonicalOctadLift,cocodePairing]

/-- The actual cocode action is diagonal in the retained rational coordinates. -/
theorem rationalCoordinateEquiv_cocode (d : Cocode) (x : Coordinates)
    (p : RationalCoordinateIndex) :
    rationalCoordinateEquiv (parkerCoordinateAction (parkerCocodeStandard d) x) p =
      rationalBitSign (cocodePairing (rationalCoordinateGolayWord p) d) *
        rationalCoordinateEquiv x p := by
  change scalarRealThetaFunEquiv
    (parkerSignedMonomial (parkerStandardParity (parkerCocodeStandard d)).toAdd
      (parkerCoordinateEquiv (parkerCocodeStandard d))
      (parkerCoordinateSign (parkerCocodeStandard d)) x p.1) p.2 = _
  rw [parkerCoordinateEquiv_cocode,parkerStandardParity_cocode]
  rw [parkerSignedMonomial_apply]
  change scalarRealThetaFunEquiv (parkerScalarSign _ * scalarParityAut (cocodeParity d) (x p.1)) p.2 = _
  rw [scalarRealThetaFunEquiv_signed,parkerCoordinateSign_cocode]
  congr 2
  unfold rationalCoordinateGolayWord
  change (cocodeDualEquiv d) _ + (if p.2=0 then 0 else cocodeParity d) =
    (cocodeDualEquiv d) (_ + if p.2=0 then 0 else golayOne)
  rw [map_add]
  split_ifs <;> simp [cocodeParity] <;> rfl

end Atlas.Fischer
