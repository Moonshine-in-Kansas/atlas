import Atlas.LinearGroups.Triality.WeylGenerators
import Atlas.LinearGroups.Triality.TraceCommutator

/-! Weyl conjugations tying the trace commutator to the defining generators. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

set_option maxHeartbeats 2000000 in
theorem middleRoot_intertwine (t : K) :
    shortWeyl F K * longWeyl F K * shortRoot F K (-t) =
      middleRoot F K t * (shortWeyl F K * longWeyl F K) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (shortWeyl F K).val ((longWeyl F K).val ((shortRoot F K (-t)).val x)) =
    (middleRoot F K t).val ((shortWeyl F K).val ((longWeyl F K).val x))
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [shortWeyl_apply, longWeyl_apply, shortRoot, middleRoot, pinnedRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f] <;> ring

set_option maxHeartbeats 2000000 in
theorem highLongRoot_intertwine (b : F) :
    shortWeyl F K * longRoot F K (-b) = highLongRoot F K b * shortWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (shortWeyl F K).val ((longRoot F K (-b)).val x) =
    (highLongRoot F K b).val ((shortWeyl F K).val x)
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [shortWeyl_apply, longRoot, highLongRoot, pinnedRoot, differenceRoot_apply,
      sumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2000000 in
theorem longNegativeRoot_intertwine (b : F) :
    longWeyl F K * longRoot F K (-b) = longNegativeRoot F K b * longWeyl F K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (longWeyl F K).val ((longRoot F K (-b)).val x) =
    (longNegativeRoot F K b).val ((longWeyl F K).val x)
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [longWeyl_apply, longRoot, longNegativeRoot, pinnedRoot, pinnedNegativeRoot,
      differenceRoot_apply, e, f, Algebra.smul_def] <;> ring

theorem middleRoot_mem (t : K) : middleRoot F K t ∈ generated F K := by
  have hw := Subgroup.mul_mem (generated F K) (shortWeyl_mem F K) (longWeyl_mem F K)
  have h := Subgroup.mul_mem (generated F K) hw (shortRoot_mem F K (-t))
  rw [middleRoot_intertwine] at h
  exact (Subgroup.mul_mem_cancel_right (generated F K) hw).mp h

theorem highLongRoot_mem (b : F) : highLongRoot F K b ∈ generated F K := by
  have h := Subgroup.mul_mem (generated F K) (shortWeyl_mem F K) (longRoot_mem F K (-b))
  rw [highLongRoot_intertwine] at h
  exact (Subgroup.mul_mem_cancel_right (generated F K) (shortWeyl_mem F K)).mp h

end Atlas.Triality
