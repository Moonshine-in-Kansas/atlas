import Atlas.Fischer.OctadicRootCoordinates
import Atlas.Fischer.AxisSums

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def octadAxisSum (O : Octad) : Coordinates := ∑ i ∈ O.val, u i
def octadExteriorAxisSum (O : Octad) : Coordinates := ∑ i ∈ O.valᶜ, u i

theorem octadAxisSum_add_exterior (O : Octad) : octadAxisSum O + octadExteriorAxisSum O = axisSum :=
  Finset.sum_add_sum_compl O.val u

theorem octadicAxisPart_eq (O : Octad) :
    octadicAxisPart O = axisSum - (2 : Scalar) • octadAxisSum O := by
  rw [← octadAxisSum_add_exterior O]
  change -octadAxisSum O + octadExteriorAxisSum O = _
  module

theorem product_axisSum_octadAxisSum (O : Octad) :
    product axisSum (octadAxisSum O) = (1 / 2 : Scalar) • axisSum + (2 : Scalar) • octadAxisSum O := by
  rw [octadAxisSum, product_sum_right]
  simp only [product_comm axisSum, product_u_axisSum, Finset.sum_add_distrib,
    Finset.sum_const, octad_size O.val O.property, ← Finset.smul_sum]
  change (8 : ℕ) • ((1 / 16 : Scalar) • axisSum) + (2 : Scalar) • octadAxisSum O =
    (1 / 2 : Scalar) • axisSum + (2 : Scalar) • octadAxisSum O
  module

theorem axisBasisProduct_octad_total (O : Octad) (i : Omega) (hi : i ∈ O.val) :
    (∑ j ∈ O.val, axisBasisProduct i j) =
      (1 / 16 : Scalar) • axisSum + (1 / 8 : Scalar) • octadAxisSum O := by
  simp only [axisBasisProduct_normalForm, ← Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_ite_eq, hi, ite_true, Finset.sum_const, octad_size O.val O.property]
  change (1 / 128 : Scalar) •
    ((8 : ℕ) • -axisSum + (16 : Scalar) • ((8 : ℕ) • u i) +
      (16 : Scalar) • octadAxisSum O + ((16 : Scalar) • axisSum - (128 : Scalar) • u i)) = _
  module

theorem product_octadAxisSum_self (O : Octad) :
    product (octadAxisSum O) (octadAxisSum O) =
      (1 / 2 : Scalar) • axisSum + octadAxisSum O := by
  rw [octadAxisSum, product_sum_left]
  simp only [product_sum_right, product_u]
  rw [Finset.sum_congr rfl (axisBasisProduct_octad_total O), Finset.sum_const,
    octad_size O.val O.property]
  change (8 : ℕ) • ((1 / 16 : Scalar) • axisSum + (1 / 8 : Scalar) • octadAxisSum O) =
    (1 / 2 : Scalar) • axisSum + octadAxisSum O
  module

/-- First row of the exact octadic square table. -/
theorem product_octadicAxisPart_self (O : Octad) :
    product (octadicAxisPart O) (octadicAxisPart O) =
      (-1 / 2 : Scalar) • octadAxisSum O + (7 / 2 : Scalar) • octadExteriorAxisSum O := by
  rw [octadicAxisPart_eq]
  simp only [product_sub_left, product_sub_right, product_smul_left, product_smul_right]
  rw [product_axisSum_self, product_axisSum_octadAxisSum,
    product_comm (octadAxisSum O) axisSum, product_axisSum_octadAxisSum,
    product_octadAxisSum_self]
  norm_num only [star_ofNat]
  rw [← octadAxisSum_add_exterior O]
  module

end Atlas.Fischer
