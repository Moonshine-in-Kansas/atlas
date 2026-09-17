import Atlas.Fischer.EmptyResidueComparison
import Atlas.Fischer.ResidueRankThree

namespace Atlas.Fischer

/-- The largest actual ray group acts primitively. This transfers the proved
empty-residue action and makes no claim about the positive subgroup's rank. -/
theorem rootGeneratedRayGroup_primitive :
    MulAction.IsPreprimitive rootGeneratedRayGroup DisplayedReflectingRay :=
  rootGeneratedRay_primitive_of_empty_residue (residueGroup_primitive ∅ (by simp))

end Atlas.Fischer
