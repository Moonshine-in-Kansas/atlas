import Atlas.LinearGroups.Triality.PositiveRoots

/-! Exact positive-root conjugations by the simple Weyl representatives.
All coefficients and signs are checked on the actual quadratic eight-space. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

set_option maxHeartbeats 2500000 in
-- Check eight coordinate identities without a characteristic restriction.
theorem shortWeyl_nextShort (t : K) :
    shortWeyl F K * nextShortRoot F K t = middleRoot F K (-t) * shortWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, shortWeyl_apply,
      nextShortRoot, middleRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2500000 in
-- Check eight coordinate identities without a characteristic restriction.
theorem shortWeyl_middle (t : K) :
    shortWeyl F K * middleRoot F K t = nextShortRoot F K (t) * shortWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, shortWeyl_apply,
      middleRoot, nextShortRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2500000 in
-- Check eight coordinate identities without a characteristic restriction.
theorem shortWeyl_highLong (t : F) :
    shortWeyl F K * highLongRoot F K t = longRoot F K (t) * shortWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, shortWeyl_apply,
      highLongRoot, longRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2500000 in
-- Check eight coordinate identities without a characteristic restriction.
theorem shortWeyl_highest (t : F) :
    shortWeyl F K * highestRoot F K t = highestRoot F K (t) * shortWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, shortWeyl_apply,
      highestRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2500000 in
-- Check eight coordinate identities without a characteristic restriction.
theorem longWeyl_nextShort (t : K) :
    longWeyl F K * nextShortRoot F K t = shortRoot F K (-t) * longWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, longWeyl_apply,
      nextShortRoot, shortRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2500000 in
-- Check eight coordinate identities without a characteristic restriction.
theorem longWeyl_middle (t : K) :
    longWeyl F K * middleRoot F K t = middleRoot F K (t) * longWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, longWeyl_apply,
      middleRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2500000 in
-- Check eight coordinate identities without a characteristic restriction.
theorem longWeyl_highest (t : F) :
    longWeyl F K * highestRoot F K t = highLongRoot F K (-t) * longWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, longWeyl_apply,
      highestRoot, highLongRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2500000 in
-- Check eight coordinate identities without a characteristic restriction.
theorem shortWeyl_short (t : K) :
    shortWeyl F K * shortRoot F K t = shortNegativeRoot F K (-t) * shortWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i|i <;> fin_cases i <;>
    simp [Subgroup.coe_mul, LinearEquiv.mul_apply, shortWeyl_apply,
      shortRoot, shortNegativeRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

end Atlas.Triality
