import Atlas.Fischer.ScalarGeometry
import Atlas.Codes.WittDesign
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Atlas.Fischer
open Atlas.Algebra Atlas.Codes

/-- The marked coordinate axes and the actual retained Golay octads. -/
abbrev CoordinateIndex := Omega ⊕ Octad
/-- Exact section coordinates for U ⊕ W, before specifying the Parker product. -/
abbrev Coordinates := CoordinateIndex → Scalar

noncomputable instance : Fintype CoordinateIndex := by
  classical
  exact inferInstanceAs (Fintype (Omega ⊕ Octad))

theorem coordinateIndex_card : Fintype.card CoordinateIndex = 783 := by
  classical
  change Fintype.card (Omega ⊕ Octad) = 783
  rw [Fintype.card_sum]
  have ho : Fintype.card Octad = 759 := by
    rw [Fintype.card_coe, octads_card]
  rw [ho]
  norm_num [Omega, HexIndex, Tetrad]

theorem coordinates_dimension : Module.finrank Scalar Coordinates = 783 := by
  rw [Module.finrank_fintype_fun_eq_card, coordinateIndex_card]

abbrev AxisCoordinates := Omega → Scalar
abbrev OctadCoordinates := Octad → Scalar

/-- The explicit splitting into the 24 and 759 coordinate summands. -/
noncomputable def coordinatesSplit : Coordinates ≃ₗ[Scalar] AxisCoordinates × OctadCoordinates :=
  LinearEquiv.sumArrowLequivProdArrow Omega Octad Scalar Scalar

theorem axisCoordinates_dimension : Module.finrank Scalar AxisCoordinates = 24 := by
  rw [Module.finrank_fintype_fun_eq_card]
  norm_num [Omega, HexIndex, Tetrad]

theorem octadCoordinates_dimension : Module.finrank Scalar OctadCoordinates = 759 := by
  classical
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, octads_card]

def coordinateWeight : CoordinateIndex → ℚ
  | Sum.inl _ => 1 / 8
  | Sum.inr _ => 1

theorem coordinateWeight_positive (i : CoordinateIndex) : 0 < coordinateWeight i := by
  cases i <;> norm_num [coordinateWeight]

noncomputable def hermitian (x y : Coordinates) : Scalar := weightedHermitian coordinateWeight x y

theorem hermitian_add_left (x y z : Coordinates) :
    hermitian (x + y) z = hermitian x z + hermitian y z :=
  weightedHermitian_add_left _ _ _ _

theorem hermitian_smul_left (a : Scalar) (x y : Coordinates) :
    hermitian (a • x) y = a * hermitian x y := weightedHermitian_smul_left _ _ _ _

theorem hermitian_smul_right (a : Scalar) (x y : Coordinates) :
    hermitian x (a • y) = star a * hermitian x y := weightedHermitian_smul_right _ _ _ _

theorem hermitian_star (x y : Coordinates) : star (hermitian x y) = hermitian y x :=
  weightedHermitian_star _ _ _

theorem hermitian_positive (x : Coordinates) (hx : x ≠ 0) :
    0 < (scalarToComplex (hermitian x x)).re := by
  rw [scalarToComplex_real]
  exact_mod_cast weightedHermitian_positive coordinateWeight coordinateWeight_positive x hx

theorem hermitian_nondegenerate (x : Coordinates)
    (hx : ∀ y, hermitian x y = 0) : x = 0 := by
  by_contra hn
  have hp := hermitian_positive x hn
  rw [hx, map_zero] at hp
  norm_num at hp

noncomputable def coordinateVector (i : CoordinateIndex) : Coordinates := Pi.single i 1
noncomputable def u (i : Omega) : Coordinates := coordinateVector (.inl i)
noncomputable def xOctad (O : Octad) : Coordinates := coordinateVector (.inr O)
noncomputable def scaledAxis (i : Omega) : Coordinates := (8 : Scalar) • u i

theorem hermitian_coordinateVector (i j : CoordinateIndex) :
    hermitian (coordinateVector i) (coordinateVector j) =
      if i = j then (coordinateWeight i : Scalar) else 0 := by
  classical
  by_cases h : i = j <;> simp [hermitian, weightedHermitian, coordinateVector, Pi.single_apply, h]

@[simp] theorem hermitian_u (i j : Omega) :
    hermitian (u i) (u j) = if i = j then 1 / 8 else 0 := by
  simp [u, hermitian_coordinateVector, coordinateWeight]

@[simp] theorem hermitian_xOctad (O P : Octad) :
    hermitian (xOctad O) (xOctad P) = if O = P then 1 else 0 := by
  simp [xOctad, hermitian_coordinateVector, coordinateWeight]

@[simp] theorem hermitian_u_xOctad (i : Omega) (O : Octad) :
    hermitian (u i) (xOctad O) = 0 := by
  simp [u, xOctad, hermitian_coordinateVector]

/-- The manuscript's basic roots as vectors; the product equation comes later. -/
def basicAxis (i : Omega) : Coordinates
  | Sum.inl j => if j = i then -7 else 1
  | Sum.inr _ => 0

theorem basicAxis_norm (i : Omega) : hermitian (basicAxis i) (basicAxis i) = 9 := by
  classical
  have he (j : Omega) :
      (1 / 8 : Scalar) * (if j = i then -7 else 1) *
        star (if j = i then (-7 : Scalar) else 1) =
      1 / 8 + if j = i then 6 else 0 := by
    split_ifs <;> norm_num
  change (∑ j : Omega ⊕ Octad, (coordinateWeight j : Scalar) * basicAxis i j * star (basicAxis i j)) = 9
  simp only [Fintype.sum_sum_type, coordinateWeight,
    basicAxis, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  simp only [he, Finset.sum_add_distrib]
  norm_num [Omega, HexIndex, Tetrad]

end Atlas.Fischer
