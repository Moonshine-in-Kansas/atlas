import Atlas.LinearGroups.Triality.AbsoluteRoots

noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable {K : Type*} [Field K]

set_option maxHeartbeats 2000000 in
theorem pinnedRoot_outer_commute (i j : Fin 4) (hi : i ≠ 1) (hj : j ≠ 1) (a b : K) :
    Commute (pinnedRoot i a) (pinnedRoot j b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (pinnedRoot i a).val ((pinnedRoot j b).val x) =
    (pinnedRoot j b).val ((pinnedRoot i a).val x)
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    ext k
    rcases k with k | k <;> fin_cases k <;>
      simp [pinnedRoot, differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply,
        e, f, Pi.single_apply] <;> ring

set_option maxHeartbeats 2000000 in
theorem pinnedNegativeRoot_outer_commute (i j : Fin 4) (hi : i ≠ 1) (hj : j ≠ 1) (a b : K) :
    Commute (pinnedNegativeRoot i a) (pinnedNegativeRoot j b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (pinnedNegativeRoot i a).val ((pinnedNegativeRoot j b).val x) =
    (pinnedNegativeRoot j b).val ((pinnedNegativeRoot i a).val x)
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    ext k
    rcases k with k | k <;> fin_cases k <;>
      simp [pinnedNegativeRoot, differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply,
        e, f, Pi.single_apply] <;> ring

end Atlas.Triality
