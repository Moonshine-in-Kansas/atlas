import Atlas.Fischer.ParkerCoordinateAction
import Atlas.Fischer.AxisProductCoefficients
import Atlas.Fischer.ProductTable

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerCoordinateAction_at_image (e : ParkerStandardGroup) (x : Coordinates)
    (i : CoordinateIndex) :
    parkerCoordinateAction e x (parkerCoordinateEquiv e i) =
      parkerScalarSign (parkerCoordinateSign e i) *
        scalarParityAut (parkerStandardParity e).toAdd (x i) := by
  simp [parkerCoordinateAction, parkerSignedMonomial]

theorem parkerOctadAction_mem (e : ParkerStandardGroup) (O : Octad) (i : Omega) :
    (parkerStandardProjection e).val i ∈ (parkerOctadAction e O).val ↔ i ∈ O.val := by
  classical
  simp [parkerOctadAction, permuteBlock]

theorem parkerCoordinateAction_axisProduct (e : ParkerStandardGroup) (i j : Omega) :
    parkerCoordinateAction e (axisBasisProduct i j) =
      axisBasisProduct ((parkerStandardProjection e).val i) ((parkerStandardProjection e).val j) := by
  classical
  funext k
  obtain ⟨l, rfl⟩ := (parkerCoordinateEquiv e).surjective k
  rw [parkerCoordinateAction_at_image]
  cases l with
  | inl p =>
    change parkerScalarSign 0 * scalarParityAut (parkerStandardParity e).toAdd
      (axisBasisProduct i j (.inl p)) =
      axisBasisProduct ((parkerStandardProjection e).val i) ((parkerStandardProjection e).val j)
        (.inl ((parkerStandardProjection e).val p))
    simp [axisBasisProduct_axis_apply, parkerScalarSign, map_ofNat]
    split_ifs <;> simp [map_ofNat]
  | inr O =>
    change _ = axisBasisProduct _ _ (.inr (parkerOctadAction e O))
    simp

theorem product_u_signedOctad (i : Omega) (d : SignedOctad) :
    product (u i) (signedOctadVector d) =
      (if i ∈ (signedOctadSupport d).val then (3 / 16 : Scalar) else -1 / 16) •
        signedOctadVector d := by
  classical
  rw [signedOctadVector, product_smul_right, parkerScalarSign_star, product_u_xOctad]
  unfold axisOctadBasisProduct
  module

theorem parkerCoordinateAction_axisOctadProduct (e : ParkerStandardGroup) (i : Omega) (O : Octad) :
    parkerCoordinateAction e (product (u i) (xOctad O)) =
      product (parkerCoordinateAction e (u i)) (parkerCoordinateAction e (xOctad O)) := by
  classical
  rw [product_u_xOctad, parkerCoordinateAction_u, parkerCoordinateAction_xOctad,
    product_u_signedOctad, parkerSignedOctadAction_support, parkerSignedOctadSupport_canonical]
  unfold axisOctadBasisProduct
  rw [map_smulₛₗ, parkerCoordinateAction_xOctad]
  simp only [parkerOctadAction_mem]
  by_cases hi : i ∈ O.val <;> simp [hi, map_ofNat]

end Atlas.Fischer
