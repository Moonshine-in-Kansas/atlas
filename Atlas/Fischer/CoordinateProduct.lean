import Atlas.Fischer.OctadProducts

namespace Atlas.Fischer
open Atlas.Codes

/-- Exact u-coordinate table, with E_i=8u_i already accounted for. -/
noncomputable def axisBasisProduct (i j : Omega) : Coordinates := by
  classical
  exact (1 / 128 : Scalar) •
    if i = j then (-81 : Scalar) • u i + (15 : Scalar) • ∑ k ∈ Finset.univ.erase i, u k
    else (15 : Scalar) • u i + (15 : Scalar) • u j -
      ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), u k

noncomputable def axisOctadBasisProduct (i : Omega) (O : Octad) : Coordinates := by
  classical
  exact (if i ∈ O.val then (3 / 16 : Scalar) else -1 / 16) • xOctad O

/-- The exact signed octad table; no associative product is imposed on A. -/
noncomputable def octadBasisProduct (O P : Octad) : Coordinates := by
  classical
  exact if O = P then
    (1 / 2 : Scalar) • ((3 : Scalar) • ∑ i ∈ O.val, u i - ∑ i ∈ O.valᶜ, u i)
  else if h4 : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 4 then
    (1 / 2 : Scalar) • signedOctadVector
      (octadProductFour (canonicalOctadLift O) (canonicalOctadLift P) h4)
  else if h0 : signedOctadIntersection (canonicalOctadLift O) (canonicalOctadLift P) = 0 then
    (theta / 2 : Scalar) • signedOctadVector
      (octadProductDisjoint (canonicalOctadLift O) (canonicalOctadLift P) h0)
  else 0

noncomputable def basisProduct : CoordinateIndex → CoordinateIndex → Coordinates
  | Sum.inl i, Sum.inl j => axisBasisProduct i j
  | Sum.inl i, Sum.inr O => axisOctadBasisProduct i O
  | Sum.inr O, Sum.inl i => axisOctadBasisProduct i O
  | Sum.inr O, Sum.inr P => octadBasisProduct O P

/-- The conjugate-bilinear extension of the exact source table. -/
noncomputable def product (x y : Coordinates) : Coordinates :=
  ∑ i, ∑ j, (star (x i) * star (y j)) • basisProduct i j

theorem product_add_left (x y z : Coordinates) :
    product (x + y) z = product x z + product y z := by
  simp [product, add_mul, add_smul, Finset.sum_add_distrib]

theorem product_add_right (x y z : Coordinates) :
    product x (y + z) = product x y + product x z := by
  simp [product, mul_add, add_smul, Finset.sum_add_distrib]

theorem product_smul_left (a : Scalar) (x y : Coordinates) :
    product (a • x) y = star a • product x y := by
  simp only [product, Pi.smul_apply, smul_eq_mul, star_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  ring

theorem product_smul_right (a : Scalar) (x y : Coordinates) :
    product x (a • y) = star a • product x y := by
  simp only [product, Pi.smul_apply, smul_eq_mul, star_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  ring

theorem product_coordinateVector (i j : CoordinateIndex) :
    product (coordinateVector i) (coordinateVector j) = basisProduct i j := by
  classical
  have hs (k l : CoordinateIndex) : star (if k = l then (1 : Scalar) else 0) =
      if k = l then 1 else 0 := by split_ifs <;> simp
  simp only [product, coordinateVector, Pi.single_apply, hs, ite_mul, mul_ite,
    one_mul, zero_mul, mul_one, mul_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Atlas.Fischer
