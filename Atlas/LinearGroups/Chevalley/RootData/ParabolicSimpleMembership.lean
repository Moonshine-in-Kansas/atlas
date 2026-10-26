import Atlas.LinearGroups.Chevalley.RootData.ParabolicWordReduction
import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength

/-! The actual root parabolic remembers precisely its generating simple nodes.
The proof reduces a word for a simple reflection to length one and uses actual
root signs to distinguish simple reflections. No Coxeter presentation is used. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem simpleWeylReflection_injective :
    Function.Injective (simpleWeylReflection P b) := by
  intro i j h
  have he : P.reflectionPerm i.val i.val = P.reflectionPerm j.val i.val :=
    congrArg (fun w : P.weylGroupToPerm.range => w.val i.val) h
  apply Subtype.ext
  apply (positive_reflection_negative_iff P b j
    (b.isPos_of_mem_support i.property)).mp
  rw [← he]
  exact not_isPos_reflection_simple P b i

theorem rootWeylLength_simple (i : b.support) :
    rootWeylLength P b (simpleWeylReflection P b i) = 1 := by
  have hp : b.IsPos ((1 : P.weylGroupToPerm.range).val i.val) :=
    b.isPos_of_mem_support i.property
  simpa only [one_mul, rootWeylLength_one, zero_add] using
    rootWeylLength_mul_simple_of_positive P b 1 i hp

theorem simpleWeylReflection_mem_rootParabolic_iff
    (J : Finset b.support) (i : b.support) :
    simpleWeylReflection P b i ∈ rootParabolicSubgroup P b J ↔ i ∈ J := by
  constructor
  · intro hi
    obtain ⟨l, hl, heq, hred⟩ := rootParabolic_exists_reduced_word P b J
      (simpleWeylReflection P b i) hi
    change rootWeylLength P b (rootWeylWord P b l) = l.length at hred
    rw [heq, rootWeylLength_simple] at hred
    cases l with
    | nil => simp at hred
    | cons j l =>
      have hn : l = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hred; omega)
      subst l
      have hj : j = i := simpleWeylReflection_injective P b (by
        simpa only [rootWeylWord, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one] using heq)
      subst j
      exact hl i List.mem_cons_self
  · intro hi
    exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem rootParabolicSubgroup_le_iff (J L : Finset b.support) :
    rootParabolicSubgroup P b J ≤ rootParabolicSubgroup P b L ↔ J ⊆ L := by
  constructor
  · intro h i hi
    exact (simpleWeylReflection_mem_rootParabolic_iff P b L i).mp
      (h ((simpleWeylReflection_mem_rootParabolic_iff P b J i).mpr hi))
  · intro h
    apply Subgroup.closure_mono
    rintro g ⟨i, hi, rfl⟩
    exact ⟨i, h hi, rfl⟩

end Atlas.Chevalley.RootData
