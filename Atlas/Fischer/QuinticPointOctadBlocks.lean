import Atlas.Fischer.QuinticPointDecomposition
import Atlas.Fischer.QuinticPointUWW

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- Actual ordered UUU/UWW internal block for external indices p,D,D. -/
def quinticPointOctadUUU_UWW (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Omega, ∑ j : Omega, ∑ k : Omega, ∑ a : Omega, ∑ b : Octad, ∑ c : Octad,
    coordinateQuinticTerm (.inl i) (.inl j) (.inl k) (.inl a) (.inr b) (.inr c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered UWW/UUU internal block for external indices p,D,D. -/
def quinticPointOctadUWW_UUU (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Omega, ∑ j : Octad, ∑ k : Octad, ∑ a : Omega, ∑ b : Omega, ∑ c : Omega,
    coordinateQuinticTerm (.inl i) (.inr j) (.inr k) (.inl a) (.inl b) (.inl c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered UWW/UWW internal block for external indices p,D,D. -/
def quinticPointOctadUWW_UWW (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Omega, ∑ j : Octad, ∑ k : Octad, ∑ a : Omega, ∑ b : Octad, ∑ c : Octad,
    coordinateQuinticTerm (.inl i) (.inr j) (.inr k) (.inl a) (.inr b) (.inr c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered WUW/WWU internal block for external indices p,D,D. -/
def quinticPointOctadWUW_WWU (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Omega, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Omega,
    coordinateQuinticTerm (.inr i) (.inl j) (.inr k) (.inr a) (.inr b) (.inl c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered WUW/WWW internal block for external indices p,D,D. -/
def quinticPointOctadWUW_WWW (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Omega, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad,
    coordinateQuinticTerm (.inr i) (.inl j) (.inr k) (.inr a) (.inr b) (.inr c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered WWU/WUW internal block for external indices p,D,D. -/
def quinticPointOctadWWU_WUW (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Omega, ∑ a : Octad, ∑ b : Omega, ∑ c : Octad,
    coordinateQuinticTerm (.inr i) (.inr j) (.inl k) (.inr a) (.inl b) (.inr c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered WWU/WWW internal block for external indices p,D,D. -/
def quinticPointOctadWWU_WWW (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Omega, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad,
    coordinateQuinticTerm (.inr i) (.inr j) (.inl k) (.inr a) (.inr b) (.inr c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered WWW/WUW internal block for external indices p,D,D. -/
def quinticPointOctadWWW_WUW (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Omega, ∑ c : Octad,
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inr a) (.inl b) (.inr c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered WWW/WWU internal block for external indices p,D,D. -/
def quinticPointOctadWWW_WWU (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Omega,
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inr a) (.inr b) (.inl c) (.inl p) (.inr D) (.inr D)

/-- Actual ordered WWW/WWW internal block for external indices p,D,D. -/
def quinticPointOctadWWW_WWW (p : Omega) (D : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad,
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inr a) (.inr b) (.inr c) (.inl p) (.inr D) (.inr D)

/-- The exact 64 point/octad type split has ten surviving ordered blocks.
Every vanished block is killed by the retained cubic table. -/
theorem coordinateQuintic_point_octad_blocks (p : Omega) (D : Octad) :
    coordinateQuintic (.inl p) (.inr D) (.inr D) =
      quinticPointOctadUUU_UWW p D +
      quinticPointOctadUWW_UUU p D +
      quinticPointOctadUWW_UWW p D +
      quinticPointOctadWUW_WWU p D +
      quinticPointOctadWUW_WWW p D +
      quinticPointOctadWWU_WUW p D +
      quinticPointOctadWWU_WWW p D +
      quinticPointOctadWWW_WUW p D +
      quinticPointOctadWWW_WWU p D +
      quinticPointOctadWWW_WWW p D := by
  classical
  unfold coordinateQuintic quinticPointOctadUUU_UWW quinticPointOctadUWW_UUU quinticPointOctadUWW_UWW quinticPointOctadWUW_WWU quinticPointOctadWUW_WWW quinticPointOctadWWU_WUW quinticPointOctadWWU_WWW quinticPointOctadWWW_WUW quinticPointOctadWWW_WWU quinticPointOctadWWW_WWW
    coordinateQuinticTerm coordinateQuinticCubicProduct
  simp (maxSteps := 200000) only [Fintype.sum_sum_type, Finset.sum_add_distrib,
    coordinateCubic_two_points_octad, coordinateCubic_point_octad_point,
    coordinateCubic_octad_two_points, star_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero]
  simp only [mul_assoc, add_assoc]
  ac_rfl

end Atlas.Fischer
