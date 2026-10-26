import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.R0
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.R1
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.R2
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.R3
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.R4
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.R5
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.R6
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.R7
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.S0
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.S1
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.S2
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.S3
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.S4
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.S5
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.S6
import Atlas.LinearGroups.ReeF4.WeylPermutationChecks.S7
/-! Sixteen coordinate Weyl permutations multiply dihedrally. No finite-field
group is enumerated; each bounded row concerns only this local Weyl action. -/
namespace Atlas.ReeF4
 theorem weylDihedralPermutation_mul : ∀ a b : DihedralGroup 8,
    weylDihedralPermutation (a*b) = weylDihedralPermutation a * weylDihedralPermutation b := by
  intro a b
  fin_cases a
  · exact weylDihedralPermutation_mul_R0 b
  · exact weylDihedralPermutation_mul_R1 b
  · exact weylDihedralPermutation_mul_R2 b
  · exact weylDihedralPermutation_mul_R3 b
  · exact weylDihedralPermutation_mul_R4 b
  · exact weylDihedralPermutation_mul_R5 b
  · exact weylDihedralPermutation_mul_R6 b
  · exact weylDihedralPermutation_mul_R7 b
  · exact weylDihedralPermutation_mul_S0 b
  · exact weylDihedralPermutation_mul_S1 b
  · exact weylDihedralPermutation_mul_S2 b
  · exact weylDihedralPermutation_mul_S3 b
  · exact weylDihedralPermutation_mul_S4 b
  · exact weylDihedralPermutation_mul_S5 b
  · exact weylDihedralPermutation_mul_S6 b
  · exact weylDihedralPermutation_mul_S7 b
end Atlas.ReeF4
