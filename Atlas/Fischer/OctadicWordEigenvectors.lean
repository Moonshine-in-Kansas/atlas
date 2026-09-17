import Atlas.Fischer.OctadicWordExpansion
import Atlas.Fischer.GolayCommonEigenspaces

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadicWordTerm_eigenvector {O : Octad} (Q : OctadCalibration O)
    (b : octadShortenedCode O) : GolayCommonEigenvector b.val (octadicWordTerm Q b) := by
  obtain ⟨i,rfl⟩ := (octadicWordIndexEquiv O).surjective b
  intro d
  rw [rationalBitSign_smul_scalar,octadicWordTerm_index]
  rcases i with u | (u | b)
  · change parkerCoordinateAction (parkerCocodeStandard d) (octadicAxisPart O)=
      parkerScalarSign (cocodePairing 0 d) • octadicAxisPart O
    rw [parkerCocodeAction_octadicAxisPart]
    simp [cocodePairing,parkerScalarSign]
  · change parkerCoordinateAction (parkerCocodeStandard d) (theta • signedOctadVector Q.octadLift)=
      parkerScalarSign (cocodePairing (octadComplementWord O) d) •
        (theta • signedOctadVector Q.octadLift)
    rw [parkerCocodeAction_smul,scalarParityAut_theta,parkerCocodeAction_signedOctad,
      Q.lift_code,cocodePairing_octadComplement,parkerScalarSign_add,smul_smul,smul_smul]
    congr 1
    ring
  · exact parkerCocodeAction_calibratedHyperplane d Q b

/-- Each individual product term has its actual summed Golay character. -/
theorem octadicWordTerm_product_eigenvector {F G : Octad}
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (b : octadShortenedCode F) (c : octadShortenedCode G) :
    GolayCommonEigenvector (b.val+c.val) (product (octadicWordTerm Q b) (octadicWordTerm R c)) :=
  golayCommonEigenvector_product _ _ _ _ (octadicWordTerm_eigenvector Q b) (octadicWordTerm_eigenvector R c)

end Atlas.Fischer
