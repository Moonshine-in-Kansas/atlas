import Atlas.Fischer.ParkerOctadProductAction
import Atlas.Fischer.ProductTable

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

private theorem scalarSign_star (s : Bit) : star (parkerScalarSign s) = parkerScalarSign s := by
  unfold parkerScalarSign
  split_ifs <;> simp

theorem product_signed_sections_four (s t : Bit) (O P : Octad) (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 4) :
    (2 : Scalar) • product
      (signedOctadVector (signedOctadSign s (canonicalOctadLift O)))
      (signedOctadVector (signedOctadSign t (canonicalOctadLift P))) =
    signedOctadVector (octadProductFour
      (signedOctadSign s (canonicalOctadLift O))
      (signedOctadSign t (canonicalOctadLift P)) h) := by
  rw [signedOctadSign_vector, signedOctadSign_vector,
    signedOctadVector_canonical, signedOctadVector_canonical,
    product_smul_left, product_smul_right, scalarSign_star, scalarSign_star,
    (octadProductFour_sign s t _ _ h h), signedOctadSign_vector, parkerScalarSign_add,
    ← product_octad_four O P hne h]
  module

theorem product_signed_sections_disjoint (s t : Bit) (O P : Octad) (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 0) :
    (2 : Scalar) • product
      (signedOctadVector (signedOctadSign s (canonicalOctadLift O)))
      (signedOctadVector (signedOctadSign t (canonicalOctadLift P))) =
    theta • signedOctadVector (octadProductDisjoint
      (signedOctadSign s (canonicalOctadLift O))
      (signedOctadSign t (canonicalOctadLift P)) h) := by
  rw [signedOctadSign_vector, signedOctadSign_vector,
    signedOctadVector_canonical, signedOctadVector_canonical,
    product_smul_left, product_smul_right, scalarSign_star, scalarSign_star,
    (octadProductDisjoint_sign s t _ _ h h), signedOctadSign_vector, parkerScalarSign_add]
  have hh := product_octad_disjoint O P hne h
  calc
    _ = (parkerScalarSign s * parkerScalarSign t) •
        ((2 : Scalar) • product (xOctad O) (xOctad P)) := by module
    _ = _ := by rw [hh]; module

theorem product_signed_sections_two (s t : Bit) (O P : Octad) (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 2) :
    product (signedOctadVector (signedOctadSign s (canonicalOctadLift O)))
      (signedOctadVector (signedOctadSign t (canonicalOctadLift P))) = 0 := by
  rw [signedOctadSign_vector, signedOctadSign_vector,
    signedOctadVector_canonical, signedOctadVector_canonical,
    product_smul_left, product_smul_right, product_octad_two O P hne h]
  simp

end Atlas.Fischer
