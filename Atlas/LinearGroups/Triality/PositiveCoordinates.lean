import Atlas.LinearGroups.Triality.PositiveRoots

/-! Recoverable six-parameter positive products in the actual eight-dimensional matrices. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def positiveWord (a : K) (b : F) (c d : K) (u v : F) : O_DPlus 4 K :=
  shortRoot F K a * longRoot F K b * nextShortRoot F K c * middleRoot F K d *
    highLongRoot F K u * highestRoot F K v

theorem positiveWord_mem (a : K) (b : F) (c d : K) (u v : F) :
    positiveWord F K a b c d u v ∈ generated F K := by
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (shortRoot_mem F K a) (longRoot_mem F K b))
      (nextShortRoot_mem F K c)) (middleRoot_mem F K d)) (highLongRoot_mem F K u))
    (highestRoot_mem F K v)

set_option maxHeartbeats 2000000 in
-- Direct recovery from a specified matrix entry, without using a group order.
theorem positiveWord_entry_a (a : K) (b : F) (c d : K) (u v : F) :
    (positiveWord F K a b c d u v).val (e 1) (.inl 0) = a := by
  simp [positiveWord, shortRoot, longRoot, nextShortRoot, middleRoot, highLongRoot,
    highestRoot, pinnedRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2000000 in
-- Direct recovery from a specified matrix entry, without using a group order.
theorem positiveWord_entry_b (a : K) (b : F) (c d : K) (u v : F) :
    (positiveWord F K a b c d u v).val (e 2) (.inl 1) = algebraMap F K b := by
  simp [positiveWord, shortRoot, longRoot, nextShortRoot, middleRoot, highLongRoot,
    highestRoot, pinnedRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2000000 in
-- Direct recovery from a specified matrix entry, without using a group order.
theorem positiveWord_entry_c (a : K) (b : F) (c d : K) (u v : F) :
    (positiveWord F K a b c d u v).val (e 2) (.inl 0) = a * algebraMap F K b - c := by
  simp [positiveWord, shortRoot, longRoot, nextShortRoot, middleRoot, highLongRoot,
    highestRoot, pinnedRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2000000 in
-- Direct recovery from a specified matrix entry, without using a group order.
theorem positiveWord_entry_d (a : K) (b : F) (c d : K) (u v : F) :
    (positiveWord F K a b c d u v).val (f 2) (.inl 1) = d := by
  simp [positiveWord, shortRoot, longRoot, nextShortRoot, middleRoot, highLongRoot,
    highestRoot, pinnedRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, e, f, Algebra.smul_def] <;> ring

set_option maxHeartbeats 2000000 in
-- Direct recovery from a specified matrix entry, without using a group order.
theorem positiveWord_entry_u (a : K) (b : F) (c d : K) (u v : F) :
    (positiveWord F K a b c d u v).val (f 2) (.inl 0) = algebraMap F K u + a*d := by
  simp [positiveWord, shortRoot, longRoot, nextShortRoot, middleRoot, highLongRoot,
    highestRoot, pinnedRoot, Subgroup.coe_mul, LinearEquiv.mul_apply,
    differenceRoot_apply, sumRoot_apply, e, f, Algebra.smul_def] <;> ring

theorem highestRoot_injective : Function.Injective (highestRoot F K) := by
  intro u v h
  have he := congrArg (fun g : O_DPlus 4 K => g.val (f 1) (.inl 0)) h
  simp [highestRoot, sumRoot_apply, e, f, Algebra.smul_def] at he
  exact he

/-- Equality of the actual matrices recovers all six ordered parameters. -/
theorem positiveWord_injective (a a' : K) (b b' : F) (c c' d d' : K) (u u' v v' : F)
    (h : positiveWord F K a b c d u v = positiveWord F K a' b' c' d' u' v') :
    a=a' ∧ b=b' ∧ c=c' ∧ d=d' ∧ u=u' ∧ v=v' := by
  have ha := congrArg (fun g : O_DPlus 4 K => g.val (e 1) (.inl 0)) h
  simp only [positiveWord_entry_a] at ha
  subst a'
  have hb := congrArg (fun g : O_DPlus 4 K => g.val (e 2) (.inl 1)) h
  simp only [positiveWord_entry_b] at hb
  have hb' := (algebraMap F K).injective hb
  subst b'
  have hc := congrArg (fun g : O_DPlus 4 K => g.val (e 2) (.inl 0)) h
  simp only [positiveWord_entry_c] at hc
  have hc' : c=c' := by linear_combination -hc
  subst c'
  have hd := congrArg (fun g : O_DPlus 4 K => g.val (f 2) (.inl 1)) h
  simp only [positiveWord_entry_d] at hd
  subst d'
  have hu := congrArg (fun g : O_DPlus 4 K => g.val (f 2) (.inl 0)) h
  simp only [positiveWord_entry_u, add_left_inj] at hu
  have hu' := (algebraMap F K).injective hu
  subst u'
  have hv : v=v' := by
    apply highestRoot_injective F K
    exact mul_left_cancel (by simpa only [positiveWord] using h)
  exact ⟨rfl,rfl,rfl,rfl,rfl,hv⟩

end Atlas.Triality
