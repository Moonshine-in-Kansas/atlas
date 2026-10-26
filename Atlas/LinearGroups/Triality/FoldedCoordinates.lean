import Atlas.LinearGroups.Triality.FoldedGenerators

noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem shortRoot_coordinate (a : K) :
    (shortRoot F K a).val (e 1) (.inl 0) = a := by
  simp [shortRoot, pinnedRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Pi.single_apply, Algebra.smul_def]

theorem shortRoot_injective : Function.Injective (shortRoot F K) := by
  intro a b h
  have hc := congrArg (fun g : O_DPlus 4 K => g.val (e 1) (.inl 0)) h
  simp only [shortRoot_coordinate] at hc
  exact hc

theorem shortNegativeRoot_coordinate (a : K) :
    (shortNegativeRoot F K a).val (e 0) (.inl 1) = a := by
  simp [shortNegativeRoot, pinnedNegativeRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Pi.single_apply, Algebra.smul_def]

theorem shortNegativeRoot_injective : Function.Injective (shortNegativeRoot F K) := by
  intro a b h
  have hc := congrArg (fun g : O_DPlus 4 K => g.val (e 0) (.inl 1)) h
  simp only [shortNegativeRoot_coordinate] at hc
  exact hc

theorem longRoot_coordinate (a : F) :
    (longRoot F K a).val (e 2) (.inl 1) = algebraMap F K a := by
  simp [longRoot, pinnedRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Pi.single_apply, Algebra.smul_def]

theorem longRoot_injective : Function.Injective (longRoot F K) := by
  intro a b h
  have hc := congrArg (fun g : O_DPlus 4 K => g.val (e 2) (.inl 1)) h
  simp only [longRoot_coordinate] at hc
  exact (algebraMap F K).injective hc

theorem longNegativeRoot_coordinate (a : F) :
    (longNegativeRoot F K a).val (e 1) (.inl 2) = algebraMap F K a := by
  simp [longNegativeRoot, pinnedNegativeRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, negativeSumRoot_apply, e, f, Pi.single_apply, Algebra.smul_def]

theorem longNegativeRoot_injective : Function.Injective (longNegativeRoot F K) := by
  intro a b h
  have hc := congrArg (fun g : O_DPlus 4 K => g.val (e 1) (.inl 2)) h
  simp only [longNegativeRoot_coordinate] at hc
  exact (algebraMap F K).injective hc

end Atlas.Triality
