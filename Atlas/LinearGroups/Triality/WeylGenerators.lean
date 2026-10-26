import Atlas.LinearGroups.Triality.Basic

/-! Actual rank-one Weyl words, without assuming their squares are one. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def shortWeyl : O_DPlus 4 K := shortRoot F K 1 * shortNegativeRoot F K (-1) * shortRoot F K 1
def longWeyl : O_DPlus 4 K := longRoot F K 1 * longNegativeRoot F K (-1) * longRoot F K 1

theorem shortWeyl_mem : shortWeyl F K ∈ generated F K :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (shortRoot_mem F K _) (shortNegativeRoot_mem F K _))
    (shortRoot_mem F K _)

theorem longWeyl_mem : longWeyl F K ∈ generated F K :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (longRoot_mem F K _) (longNegativeRoot_mem F K _))
    (longRoot_mem F K _)

set_option maxHeartbeats 2000000 in
theorem shortWeyl_apply (x : VectorD 4 K) :
    (shortWeyl F K).val x =
      Sum.elim ![x (.inl 1),-x (.inl 0),-x (.inr 2),-x (.inr 3)]
        ![x (.inr 1),-x (.inr 0),-x (.inl 2),-x (.inl 3)] := by
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [shortWeyl, shortRoot, shortNegativeRoot, pinnedRoot, pinnedNegativeRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply,
      negativeSumRoot_apply, e, f] <;> ring

set_option maxHeartbeats 2000000 in
theorem longWeyl_apply (x : VectorD 4 K) :
    (longWeyl F K).val x =
      Sum.elim ![x (.inl 0),x (.inl 2),-x (.inl 1),x (.inl 3)]
        ![x (.inr 0),x (.inr 2),-x (.inr 1),x (.inr 3)] := by
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [longWeyl, longRoot, longNegativeRoot, pinnedRoot, pinnedNegativeRoot,
      Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply,
      e, f, Algebra.smul_def] <;> ring

end Atlas.Triality
