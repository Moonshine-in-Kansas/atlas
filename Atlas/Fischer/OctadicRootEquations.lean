import Atlas.Fischer.OctadicHyperplaneSquare
import Atlas.Fischer.OctadicCocodeAction
import Atlas.Fischer.ParkerMultiplicativity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadicRoot_zero_formula {O : Octad} (Q : OctadCalibration O) :
    octadicRoot Q 0 = (1 / 2 : Scalar) • (octadicAxisPart O +
      theta • signedOctadVector Q.octadLift + octadicHyperplanePart Q 0) := by
  simp [octadicRoot, octadicHyperplanePart, parkerScalarSign]

theorem product_octadicRoot_zero {O : Octad} (Q : OctadCalibration O) :
    product (octadicRoot Q 0) (octadicRoot Q 0) = (10 : Scalar) • octadicRoot Q 0 := by
  let U := octadicAxisPart O
  let T := theta • signedOctadVector Q.octadLift
  let Y := octadicHyperplanePart Q 0
  have ht : product (U + T + Y) (U + T + Y) =
      product U U + (2 : Scalar) • product U T + (2 : Scalar) • product U Y +
      product T T + (2 : Scalar) • product T Y + product Y Y := by
    simp only [product_add_left, product_add_right]
    rw [product_comm T U, product_comm Y U, product_comm Y T]
    module
  have hp : product (U + T + Y) (U + T + Y) = (20 : Scalar) • (U + T + Y) := by
    rw [ht, product_octadicAxisPart_self, product_octadicAxisPart_theta_octad,
      product_octadicAxisPart_hyperplanePart, product_theta_calibratedOctad_self,
      product_theta_octad_hyperplanePart, product_octadicHyperplanePart_self]
    change _ = (20 : Scalar) • (-octadAxisSum O + octadExteriorAxisSum O + T + Y)
    dsimp [T, Y]
    module
  rw [octadicRoot_zero_formula, product_smul_left, product_smul_right]
  change star (1 / 2 : Scalar) • (star (1 / 2 : Scalar) • product (U + T + Y) (U + T + Y)) =
    (10 : Scalar) • ((1 / 2 : Scalar) • (U + T + Y))
  rw [hp]
  norm_num
  module

/-- The square equation for every displayed phase is transported by the actual
already verified cocode subgroup of H. -/
theorem product_octadicRoot {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    product (octadicRoot Q χ) (octadicRoot Q χ) = (10 : Scalar) • octadicRoot Q χ := by
  obtain ⟨d, hd⟩ := octadicRoot_cocode_transitive Q 0 χ
  rw [← hd, ← parkerCoordinateAction_product, product_octadicRoot_zero, parkerCocodeAction_smul]
  have hn := scalarParityAut_rat (cocodeParity d) (10 : ℚ)
  norm_num at hn
  rw [hn]

theorem octadicRoot_isRoot {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    IsRoot (octadicRoot Q χ) := ⟨octadicRoot_norm Q χ, product_octadicRoot Q χ⟩

end Atlas.Fischer
