import Atlas.Algebra.BinaryQuadraticCode

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

/-- The sixteen domain points, expanded with arbitrary symbolic summands.
This enumerates neither quadratic forms nor their coefficients. -/
theorem binaryFour_sum (f : BinaryFour → Bit) :
    (∑ v, f v) =
      f ![0,0,0,0]+f ![0,0,0,1]+f ![0,0,1,0]+f ![0,0,1,1]+
      f ![0,1,0,0]+f ![0,1,0,1]+f ![0,1,1,0]+f ![0,1,1,1]+
      f ![1,0,0,0]+f ![1,0,0,1]+f ![1,0,1,0]+f ![1,0,1,1]+
      f ![1,1,0,0]+f ![1,1,0,1]+f ![1,1,1,0]+f ![1,1,1,1] := by
  have he : (Finset.univ : Finset BinaryFour) =
      {![0,0,0,0],![0,0,0,1],![0,0,1,0],![0,0,1,1],
       ![0,1,0,0],![0,1,0,1],![0,1,1,0],![0,1,1,1],
       ![1,0,0,0],![1,0,0,1],![1,0,1,0],![1,0,1,1],
       ![1,1,0,0],![1,1,0,1],![1,1,1,0],![1,1,1,1]} := by decide +kernel
  rw [he]
  simp [Finset.sum_insert]
  <;> norm_num
  <;> ring

end Atlas.Algebra
