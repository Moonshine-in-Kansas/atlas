import Atlas.Sporadic.SuzukiStructure

noncomputable section
namespace Atlas.Sporadic.Suzuki
open Atlas.Conway MulAction

/-- The full stabilizer in the actual scalar quotient is maximal. -/
theorem projective_frame_stabilizer_maximal :
    IsCoatom (stabilizer Model baseFrame) := by
  letI := primitive
  exact eisensteinProjectiveStabilizer_maximal_of_primitive

/-- A final structural consequence of established simplicity. This theorem is
not an input to the independent fusion and action-kernel arguments. -/
theorem projective_frame_stabilizer_not_normal :
    ¬ (stabilizer Model baseFrame).Normal := by
  letI := primitive
  exact eisensteinProjectiveStabilizer_not_normal_of_primitive

end Atlas.Sporadic.Suzuki
