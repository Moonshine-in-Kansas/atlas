import Atlas.LinearGroups.Triality.RootConjugation

/-! The remaining positive relative roots, obtained from literal Weyl conjugations. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The relative root s+l, with signs fixed by the central-node Weyl word. -/
def nextShortRoot (t : K) : O_DPlus 4 K :=
  differenceRoot 0 2 (by decide) (-t) *
    differenceRoot 1 3 (by decide) (FiniteCubic.sigma F K t) *
    sumRoot 1 3 (FiniteCubic.sigma F K (FiniteCubic.sigma F K t))

/-- The highest relative root 3s+2l. -/
def highestRoot (b : F) : O_DPlus 4 K := sumRoot 0 1 (algebraMap F K b)

set_option maxHeartbeats 2000000 in
-- Eight explicit coordinate identities, uniform in the coefficient field.
theorem nextShortRoot_intertwine (t : K) :
    longWeyl F K * shortRoot F K t = nextShortRoot F K t * longWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (longWeyl F K).val ((shortRoot F K t).val x) =
    (nextShortRoot F K t).val ((longWeyl F K).val x)
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [longWeyl_apply, shortRoot, nextShortRoot, pinnedRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f] <;> ring

set_option maxHeartbeats 2000000 in
-- Eight explicit coordinate identities, with no assumption on characteristic.
theorem highestRoot_intertwine (b : F) :
    longWeyl F K * highLongRoot F K b = highestRoot F K b * longWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (longWeyl F K).val ((highLongRoot F K b).val x) =
    (highestRoot F K b).val ((longWeyl F K).val x)
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [longWeyl_apply, highLongRoot, highestRoot, sumRoot_apply, e, f, Algebra.smul_def] <;> ring

theorem nextShortRoot_mem (t : K) : nextShortRoot F K t ∈ generated F K := by
  have h := Subgroup.mul_mem (generated F K) (longWeyl_mem F K) (shortRoot_mem F K t)
  rw [nextShortRoot_intertwine] at h
  exact (Subgroup.mul_mem_cancel_right (generated F K) (longWeyl_mem F K)).mp h

theorem highestRoot_mem (b : F) : highestRoot F K b ∈ generated F K := by
  have h := Subgroup.mul_mem (generated F K) (longWeyl_mem F K) (highLongRoot_mem F K b)
  rw [highestRoot_intertwine] at h
  exact (Subgroup.mul_mem_cancel_right (generated F K) (longWeyl_mem F K)).mp h

end Atlas.Triality
