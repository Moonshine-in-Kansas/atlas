import Atlas.Fischer.QuinticBlocks
import Atlas.Fischer.CubicSliceCoefficients

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

def quinticPointUUU (p q r : Omega) : Scalar :=
  ∑ i : Omega, ∑ j : Omega, ∑ k : Omega, ∑ a : Omega, ∑ b : Omega, ∑ c : Omega,
    coordinateQuinticTerm (.inl i) (.inl j) (.inl k) (.inl a) (.inl b) (.inl c)
      (.inl p) (.inl q) (.inl r)

def quinticPointWUW (p q r : Omega) : Scalar :=
  ∑ i : Octad, ∑ j : Omega, ∑ k : Octad, ∑ a : Octad, ∑ b : Omega, ∑ c : Octad,
    coordinateQuinticTerm (.inr i) (.inl j) (.inr k) (.inr a) (.inl b) (.inr c)
      (.inl p) (.inl q) (.inl r)

def quinticPointWWU (p q r : Omega) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Omega, ∑ a : Octad, ∑ b : Octad, ∑ c : Omega,
    coordinateQuinticTerm (.inr i) (.inr j) (.inl k) (.inr a) (.inr b) (.inl c)
      (.inl p) (.inl q) (.inl r)

def quinticPointWWW (p q r : Omega) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad,
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inr a) (.inr b) (.inr c)
      (.inl p) (.inl q) (.inl r)

theorem coordinateCubic_point_octad_point (i j : Omega) (D : Octad) :
    coordinateCubic (.inl i) (.inr D) (.inl j) = 0 := by
  rw [coordinateCubic_swap_last, coordinateCubic_two_points_octad]

theorem coordinateCubic_octad_two_points (D : Octad) (i j : Omega) :
    coordinateCubic (.inr D) (.inl i) (.inl j) = 0 := by
  rw [coordinateCubic_swap_first, coordinateCubic_point_octad_point]

/-- Split the six summed indices only by point/octad type. The product table
kills all but five patterns; no coordinate values are enumerated. -/
theorem coordinateQuintic_points_blocks (p q r : Omega) :
    coordinateQuintic (.inl p) (.inl q) (.inl r) =
      quinticPointUUU p q r + quinticPointUWW p q r + quinticPointWUW p q r +
        quinticPointWWU p q r + quinticPointWWW p q r := by
  classical
  unfold coordinateQuintic quinticPointUUU quinticPointUWW quinticPointWUW
    quinticPointWWU quinticPointWWW coordinateQuinticTerm coordinateQuinticCubicProduct
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib,
    coordinateCubic_two_points_octad, coordinateCubic_point_octad_point,
    coordinateCubic_octad_two_points, star_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero]
  simp only [mul_assoc, add_assoc]
  ac_rfl

end Atlas.Fischer
