import Atlas.Fischer.QuinticPointOctadBlocks

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- Actual ordered UUU/WWW internal block with three octad external indices. -/
def quinticOctadBlockUUU_WWW (D E F : Octad) : Scalar :=
  ∑ i : Omega, ∑ j : Omega, ∑ k : Omega, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad, 
    coordinateQuinticTerm (.inl i) (.inl j) (.inl k) (.inr a) (.inr b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered UWW/WUW internal block with three octad external indices. -/
def quinticOctadBlockUWW_WUW (D E F : Octad) : Scalar :=
  ∑ i : Omega, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Omega, ∑ c : Octad, 
    coordinateQuinticTerm (.inl i) (.inr j) (.inr k) (.inr a) (.inl b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered UWW/WWU internal block with three octad external indices. -/
def quinticOctadBlockUWW_WWU (D E F : Octad) : Scalar :=
  ∑ i : Omega, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Omega, 
    coordinateQuinticTerm (.inl i) (.inr j) (.inr k) (.inr a) (.inr b) (.inl c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered UWW/WWW internal block with three octad external indices. -/
def quinticOctadBlockUWW_WWW (D E F : Octad) : Scalar :=
  ∑ i : Omega, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad, 
    coordinateQuinticTerm (.inl i) (.inr j) (.inr k) (.inr a) (.inr b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WUW/UWW internal block with three octad external indices. -/
def quinticOctadBlockWUW_UWW (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Omega, ∑ k : Octad, ∑ a : Omega, ∑ b : Octad, ∑ c : Octad, 
    coordinateQuinticTerm (.inr i) (.inl j) (.inr k) (.inl a) (.inr b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WUW/WWU internal block with three octad external indices. -/
def quinticOctadBlockWUW_WWU (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Omega, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Omega, 
    coordinateQuinticTerm (.inr i) (.inl j) (.inr k) (.inr a) (.inr b) (.inl c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WUW/WWW internal block with three octad external indices. -/
def quinticOctadBlockWUW_WWW (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Omega, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad, 
    coordinateQuinticTerm (.inr i) (.inl j) (.inr k) (.inr a) (.inr b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WWU/UWW internal block with three octad external indices. -/
def quinticOctadBlockWWU_UWW (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Omega, ∑ a : Omega, ∑ b : Octad, ∑ c : Octad, 
    coordinateQuinticTerm (.inr i) (.inr j) (.inl k) (.inl a) (.inr b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WWU/WUW internal block with three octad external indices. -/
def quinticOctadBlockWWU_WUW (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Omega, ∑ a : Octad, ∑ b : Omega, ∑ c : Octad, 
    coordinateQuinticTerm (.inr i) (.inr j) (.inl k) (.inr a) (.inl b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WWU/WWW internal block with three octad external indices. -/
def quinticOctadBlockWWU_WWW (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Omega, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad, 
    coordinateQuinticTerm (.inr i) (.inr j) (.inl k) (.inr a) (.inr b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WWW/UUU internal block with three octad external indices. -/
def quinticOctadBlockWWW_UUU (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Omega, ∑ b : Omega, ∑ c : Omega, 
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inl a) (.inl b) (.inl c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WWW/UWW internal block with three octad external indices. -/
def quinticOctadBlockWWW_UWW (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Omega, ∑ b : Octad, ∑ c : Octad, 
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inl a) (.inr b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WWW/WUW internal block with three octad external indices. -/
def quinticOctadBlockWWW_WUW (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Omega, ∑ c : Octad, 
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inr a) (.inl b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WWW/WWU internal block with three octad external indices. -/
def quinticOctadBlockWWW_WWU (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Omega, 
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inr a) (.inr b) (.inl c) (.inr D) (.inr E) (.inr F)

/-- Actual ordered WWW/WWW internal block with three octad external indices. -/
def quinticOctadBlockWWW_WWW (D E F : Octad) : Scalar :=
  ∑ i : Octad, ∑ j : Octad, ∑ k : Octad, ∑ a : Octad, ∑ b : Octad, ∑ c : Octad, 
    coordinateQuinticTerm (.inr i) (.inr j) (.inr k) (.inr a) (.inr b) (.inr c) (.inr D) (.inr E) (.inr F)

/-- Exact symbolic point/octad splitting; fifteen blocks survive the actual cubic support. -/
theorem coordinateQuintic_octad_blocks (D E F : Octad) :
    coordinateQuintic (.inr D) (.inr E) (.inr F) =
      quinticOctadBlockUUU_WWW D E F +
      quinticOctadBlockUWW_WUW D E F +
      quinticOctadBlockUWW_WWU D E F +
      quinticOctadBlockUWW_WWW D E F +
      quinticOctadBlockWUW_UWW D E F +
      quinticOctadBlockWUW_WWU D E F +
      quinticOctadBlockWUW_WWW D E F +
      quinticOctadBlockWWU_UWW D E F +
      quinticOctadBlockWWU_WUW D E F +
      quinticOctadBlockWWU_WWW D E F +
      quinticOctadBlockWWW_UUU D E F +
      quinticOctadBlockWWW_UWW D E F +
      quinticOctadBlockWWW_WUW D E F +
      quinticOctadBlockWWW_WWU D E F +
      quinticOctadBlockWWW_WWW D E F := by
  classical
  unfold coordinateQuintic
    quinticOctadBlockUUU_WWW quinticOctadBlockUWW_WUW quinticOctadBlockUWW_WWU quinticOctadBlockUWW_WWW quinticOctadBlockWUW_UWW quinticOctadBlockWUW_WWU quinticOctadBlockWUW_WWW quinticOctadBlockWWU_UWW quinticOctadBlockWWU_WUW quinticOctadBlockWWU_WWW quinticOctadBlockWWW_UUU quinticOctadBlockWWW_UWW quinticOctadBlockWWW_WUW quinticOctadBlockWWW_WWU quinticOctadBlockWWW_WWW
    coordinateQuinticTerm coordinateQuinticCubicProduct
  simp (maxSteps := 200000) only [Fintype.sum_sum_type, Finset.sum_add_distrib,
    coordinateCubic_two_points_octad, coordinateCubic_point_octad_point,
    coordinateCubic_octad_two_points, star_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero]
  simp only [mul_assoc, add_assoc]
  ac_rfl

end Atlas.Fischer
