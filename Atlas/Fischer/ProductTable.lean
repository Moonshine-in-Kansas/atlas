import Atlas.Fischer.CoordinateProduct

namespace Atlas.Fischer
open Atlas.Codes

theorem product_u (i j : Omega) : product (u i) (u j) = axisBasisProduct i j :=
  product_coordinateVector _ _

theorem product_u_xOctad (i : Omega) (O : Octad) :
    product (u i) (xOctad O) = axisOctadBasisProduct i O := product_coordinateVector _ _

theorem product_xOctad_u (i : Omega) (O : Octad) :
    product (xOctad O) (u i) = axisOctadBasisProduct i O := product_coordinateVector _ _

theorem product_xOctad (O P : Octad) :
    product (xOctad O) (xOctad P) = octadBasisProduct O P := product_coordinateVector _ _

/-- Manuscript equation2.5, with its precise scaled axis normalization. -/
theorem product_scaledAxis_self (i : Omega) :
    (2 : Scalar) • product (scaledAxis i) (scaledAxis i) =
      (-81 : Scalar) • u i + (15 : Scalar) • ∑ k ∈ Finset.univ.erase i, u k := by
  classical
  rw [scaledAxis, product_smul_left, product_smul_right, product_u]
  norm_num [axisBasisProduct, smul_smul]

/-- Manuscript equation2.6. -/
theorem product_scaledAxis_distinct (i j : Omega) (h : i ≠ j) :
    (2 : Scalar) • product (scaledAxis i) (scaledAxis j) =
      (15 : Scalar) • u i + (15 : Scalar) • u j -
        ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), u k := by
  classical
  rw [scaledAxis, scaledAxis, product_smul_left, product_smul_right, product_u]
  norm_num [axisBasisProduct, h, smul_smul]

/-- Manuscript equation2.7. -/
theorem product_scaledAxis_octad (i : Omega) (O : Octad) :
    (2 : Scalar) • product (scaledAxis i) (xOctad O) =
      (if i ∈ O.val then (3 : Scalar) else -1) • xOctad O := by
  classical
  rw [scaledAxis, product_smul_left, product_u_xOctad]
  unfold axisOctadBasisProduct
  split_ifs <;> norm_num [smul_smul]

/-- Manuscript equation2.8 on the chosen signed section. -/
theorem product_octad_self (O : Octad) :
    (2 : Scalar) • product (xOctad O) (xOctad O) =
      (3 : Scalar) • ∑ i ∈ O.val, u i - ∑ i ∈ O.valᶜ, u i := by
  classical
  rw [product_xOctad]
  simp [octadBasisProduct, smul_smul]

/-- Manuscript equation2.9, intersection-four branch on the exact section. -/
theorem product_octad_four (O P : Octad) (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 4) :
    (2 : Scalar) • product (xOctad O) (xOctad P) =
      signedOctadVector (octadProductFour (canonicalOctadLift O) (canonicalOctadLift P) h) := by
  classical
  rw [product_xOctad]
  simp [octadBasisProduct, hne, h, smul_smul]

/-- Manuscript equation2.9, complementary-octad phase. -/
theorem product_octad_disjoint (O P : Octad) (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 0) :
    (2 : Scalar) • product (xOctad O) (xOctad P) =
      theta • signedOctadVector
        (octadProductDisjoint (canonicalOctadLift O) (canonicalOctadLift P) h) := by
  classical
  rw [product_xOctad]
  have ht : (2 : Scalar) * (theta / 2) = theta := by ring
  simp [octadBasisProduct, hne, h, smul_smul, ht]

theorem product_octad_two (O P : Octad) (hne : O ≠ P)
    (h : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 2) :
    product (xOctad O) (xOctad P) = 0 := by
  classical
  rw [product_xOctad]
  simp [octadBasisProduct, hne, h]

end Atlas.Fischer
