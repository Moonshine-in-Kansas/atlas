import Atlas.Fischer.DuadPureSummandCoordinates

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Before changing the global Parker section, every pure term has its literal
calibrated vector with coefficient plus or minus one half. -/
theorem duadPureTerm_sign {F G : Octad}
    (hFG : (F.val ∩ G.val).card = 2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (b : octadShortenedCode G) (hb : b ≠ 0) :
    ∃ e : Bit, product (octadicWordTerm Q 0) (octadicWordTerm R b) =
      (parkerScalarSign e / 2) • octadicWordTerm R b := by
  rw [octadicWordTerm_zero]
  by_cases hX : b = octadShortenedOne G
  · refine ⟨1, ?_⟩
    rw [hX, octadicWordTerm_one, product_smul_right,
      product_octadicAxisPart_signedOctad]
    have ho : signedOctadSupport R.octadLift = G :=
      (signedOctadSupport_eq_iff _ _).mpr R.lift_code
    rw [ho, hFG, theta_conjugate]
    norm_num only [parkerScalarSign, one_ne_zero, ite_false]
    module
  · let c : OctadShortenedHyperplane G := ⟨b, hb, hX⟩
    change ∃ e : Bit, product (octadicAxisPart F) (octadicWordTerm R c.val) =
      (parkerScalarSign e / 2) • octadicWordTerm R c.val
    rw [octadicWordTerm_hyperplane]
    change ∃ e : Bit, product (octadicAxisPart F) (signedOctadVector (calibratedHyperplaneLift R c)) =
      (parkerScalarSign e / 2) • signedOctadVector (calibratedHyperplaneLift R c)
    rw [product_octadicAxisPart_signedOctad]
    rcases duadPair_disjoint_octad_intersections F G
      (signedOctadSupport (calibratedHyperplaneLift R c)) hFG
      (calibratedHyperplaneSupport_disjoint R c) with ht | ht
    · refine ⟨0, ?_⟩
      rw [ht]
      norm_num [parkerScalarSign]
    · refine ⟨1, ?_⟩
      rw [ht]
      norm_num [parkerScalarSign]

end Atlas.Fischer
