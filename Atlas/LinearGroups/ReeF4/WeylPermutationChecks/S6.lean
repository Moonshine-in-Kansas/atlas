import Atlas.LinearGroups.ReeF4.WeylPermutationData

/-! One of sixteen bounded rows for the local coordinate Weyl multiplication. -/
namespace Atlas.ReeF4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 600000 in
theorem weylDihedralPermutation_mul_S6 : ∀ b : DihedralGroup 8,
    weylDihedralPermutation (DihedralGroup.sr 6 * b) =
      weylDihedralPermutation (DihedralGroup.sr 6) * weylDihedralPermutation b := by
  intro b
  fin_cases b <;> decide
end Atlas.ReeF4
