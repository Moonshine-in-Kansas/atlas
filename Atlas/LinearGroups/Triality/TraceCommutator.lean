import Atlas.LinearGroups.Triality.Basic

/-! The all-characteristic trace commutator for the literal pinning. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The relative root 2s+l in the pinning used here. -/
def middleRoot (t : K) : O_DPlus 4 K :=
  differenceRoot 0 3 (by decide) (FiniteCubic.sigma F K (FiniteCubic.sigma F K t)) *
    sumRoot 0 3 (FiniteCubic.sigma F K t) * sumRoot 1 2 t

/-- The relative root 3s+l. -/
def highLongRoot (b : F) : O_DPlus 4 K := sumRoot 0 2 (algebraMap F K b)

set_option maxHeartbeats 2000000 in
theorem trace_root_commutation (hdeg : Module.finrank F K = 3) (t : K) :
    shortRoot F K 1 * middleRoot F K t =
      highLongRoot F K (FiniteCubic.trace F K t) * middleRoot F K t * shortRoot F K 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (shortRoot F K 1).val ((middleRoot F K t).val x) =
    (highLongRoot F K (FiniteCubic.trace F K t)).val
      ((middleRoot F K t).val ((shortRoot F K 1).val x))
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [shortRoot, middleRoot, highLongRoot, pinnedRoot, Subgroup.coe_mul,
      LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply, e, f,
      FiniteCubic.trace_formula hdeg, Algebra.smul_def] <;> ring

end Atlas.Triality
