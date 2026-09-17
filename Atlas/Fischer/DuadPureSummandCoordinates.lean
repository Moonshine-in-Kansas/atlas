import Atlas.Fischer.OctadicWordTermValues
import Atlas.Fischer.DuadWordPairCoordinates
import Atlas.Fischer.OctadicRootFibres

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem signedOctadVector_ne_zero (d : SignedOctad) : signedOctadVector d ≠ 0 := by
  intro h
  have he := congrFun h (.inr (signedOctadSupport d))
  simp only [signedOctadVector, Pi.smul_apply, smul_eq_mul, xOctad_octad_apply,
    ite_true, mul_one, Pi.zero_apply] at he
  exact parkerScalarSign_ne_zero _ he

/-- The pure shortened-code summands of the actual product never vanish. -/
theorem duadPureSummand_product_ne_zero {F G : Octad}
    (hFG : (F.val ∩ G.val).card = 2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (b : octadShortenedCode G) (hb : b ≠ 0) :
    product (octadicWordTerm Q 0) (octadicWordTerm R b) ≠ 0 := by
  rw [octadicWordTerm_zero]
  by_cases hX : b = octadShortenedOne G
  · rw [hX, octadicWordTerm_one, product_smul_right,
      product_octadicAxisPart_signedOctad]
    have ho : signedOctadSupport R.octadLift = G :=
      (signedOctadSupport_eq_iff _ _).mpr R.lift_code
    rw [ho, hFG]
    apply smul_ne_zero
    · exact star_ne_zero.mpr theta_ne_zero
    · apply smul_ne_zero
      · norm_num
      · exact signedOctadVector_ne_zero _
  · let c : OctadShortenedHyperplane G := ⟨b, hb, hX⟩
    change product (octadicAxisPart F) (octadicWordTerm R c.val) ≠ 0
    rw [octadicWordTerm_hyperplane]
    change product (octadicAxisPart F) (signedOctadVector (calibratedHyperplaneLift R c)) ≠ 0
    rw [product_octadicAxisPart_signedOctad]
    apply smul_ne_zero
    · rcases duadPair_disjoint_octad_intersections F G
        (signedOctadSupport (calibratedHyperplaneLift R c)) hFG
        (calibratedHyperplaneSupport_disjoint R c) with ht | ht <;> rw [ht] <;> norm_num
    · exact signedOctadVector_ne_zero _

/-- A nonzero pure term has an actual nonzero rational coordinate carrying its
exact Golay word. This avoids any assumed coefficient formula. -/
theorem duadPureSummand_coordinate_exists {F G : Octad}
    (hFG : (F.val ∩ G.val).card = 2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (b : octadShortenedCode G) (hb : b ≠ 0) :
    ∃ p : RationalCoordinateIndex, rationalCoordinateGolayWord p = b.val ∧
      rationalCoordinateEquiv (product (octadicWordTerm Q 0) (octadicWordTerm R b)) p ≠ 0 := by
  have hn := duadPureSummand_product_ne_zero hFG Q R b hb
  have he := (golayCommonEigenvector_iff _ _).mp
    (octadicWordTerm_product_eigenvector Q R 0 b)
  by_contra! h
  apply hn
  apply rationalCoordinateEquiv.injective
  funext p
  simp only [map_zero, Pi.zero_apply]
  change rationalCoordinateEquiv (product (octadicWordTerm Q 0) (octadicWordTerm R b)) p = 0
  by_cases hp : rationalCoordinateGolayWord p = b.val
  · exact h p hp
  · apply he p
    simpa only [ZeroMemClass.coe_zero, zero_add] using hp

end Atlas.Fischer
