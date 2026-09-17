import Atlas.LinearGroups.ReeG2.PointCompatibility

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The Weyl matrix acts by negative coordinate reversal. -/
def negativeReverse (v : Vector F) : Vector F := ![-v 6, -v 5, -v 4, -v 3, -v 2, -v 1, -v 0]

set_option maxHeartbeats 800000 in
theorem pointCompatibility_reverse (m : ℕ) {v w : Vector F}
    (h : pointCompatibility m v w) :
    pointCompatibility m (negativeReverse v) (negativeReverse w) := by
  rcases h with ⟨⟨k0,k1,k2,k3,k4,k5,k6⟩,s0,s1,s2,s3,s4,s5,s6⟩
  simp only [wedgeCoordinate] at *
  unfold pointCompatibility exteriorKernel
  simp only [wedgeCoordinate, negativeReverse, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_neg]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · linear_combination -k6
  · linear_combination -k5
  · linear_combination -k4
  · linear_combination -k3
  · linear_combination -k2
  · linear_combination -k1
  · linear_combination -k0
  · linear_combination -s6
  · linear_combination -s5
  · linear_combination -s4
  · linear_combination -s3
  · linear_combination -s2
  · linear_combination -s1
  · linear_combination -s0

end Atlas.ReeG2
