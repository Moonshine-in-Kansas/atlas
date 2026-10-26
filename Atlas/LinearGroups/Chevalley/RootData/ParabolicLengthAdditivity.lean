import Atlas.LinearGroups.Chevalley.RootData.ParabolicWordReduction
import Atlas.LinearGroups.Chevalley.RootData.PositiveSupportedRootImage

/-! Actual right-parabolic minimality and length additivity, proved from
positive root support and the sign-controlled simple-reflection length step. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

private theorem word_preserves_support (J : Finset b.support) (l : List b.support)
    (hl : ∀ i ∈ l, i ∈ J) {β : ι}
    (hβ : (rootSimpleCoefficients P b β).support ⊆ J) :
    (rootSimpleCoefficients P b ((rootWeylWord P b l).val β)).support ⊆ J := by
  induction l generalizing β with
  | nil => exact hβ
  | cons i l ih =>
    change (rootSimpleCoefficients P b
      (P.reflectionPerm i.val ((rootWeylWord P b l).val β))).support ⊆ J
    exact rootSimpleCoefficients_reflection_support_subset P b J i
      (hl i List.mem_cons_self) _
      (ih (fun j hj => hl j (List.mem_cons_of_mem i hj)) hβ)

private theorem word_append_simple (l : List b.support) (i : b.support) :
    rootWeylWord P b (l ++ [i]) = rootWeylWord P b l * simpleWeylReflection P b i := by
  rw [rootWeylWord_append]
  simp only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- Positivity on the selected simple roots prevents cancellation against any
ambient reduced word in those generators. -/
theorem rootWeylLength_mul_reduced_parabolic_word
    (J : Finset b.support) (x : P.weylGroupToPerm.range)
    (hx : ∀ i ∈ J, b.IsPos (x.val i.val))
    (l : List b.support) (hl : ∀ i ∈ l, i ∈ J)
    (hred : IsReducedRootWord P b l) :
    rootWeylLength P b (x * rootWeylWord P b l) =
      rootWeylLength P b x + l.length := by
  induction l using List.reverseRecOn with
  | nil => simp only [rootWeylWord, List.map_nil, List.prod_nil, mul_one,
      List.length_nil, Nat.add_zero]
  | append_singleton l i ih =>
    have hi : i ∈ J := hl i (List.mem_append_right _ (List.mem_singleton_self _))
    have hlJ : ∀ j ∈ l, j ∈ J := fun j hj => hl j (List.mem_append_left _ hj)
    have hlred := (isReducedRootWord_append_parts P b l [i] hred).1
    have hβ : b.IsPos ((rootWeylWord P b l).val i.val) :=
      isReducedRootWord_prefix_label_pos P b l [] i
        (by simpa only [List.append_nil] using hred)
    have hsimple : (rootSimpleCoefficients P b i.val).support ⊆ J := by
      rw [rootSimpleCoefficients_simple,
        Finsupp.support_single i (by decide : (1 : ℤ) ≠ 0)]
      exact Finset.singleton_subset_iff.mpr hi
    have hs := word_preserves_support P b J l hlJ hsimple
    have hpos : b.IsPos ((x * rootWeylWord P b l).val i.val) :=
      rootWeyl_isPos_of_simple_support P b J x hx hβ hs
    have hstep := rootWeylLength_mul_simple_of_positive P b
      (x * rootWeylWord P b l) i hpos
    have hword : x * rootWeylWord P b (l ++ [i]) =
        (x * rootWeylWord P b l) * simpleWeylReflection P b i := by
      rw [word_append_simple, mul_assoc]
    rw [hword, hstep, ih hlJ hlred, List.length_append, List.length_singleton]
    omega

theorem rootWeylLength_mul_parabolic_of_simple_positive
    (J : Finset b.support) (x : P.weylGroupToPerm.range)
    (hx : ∀ i ∈ J, b.IsPos (x.val i.val))
    (v : P.weylGroupToPerm.range) (hv : v ∈ rootParabolicSubgroup P b J) :
    rootWeylLength P b (x * v) = rootWeylLength P b x + rootWeylLength P b v := by
  obtain ⟨l, hl, rfl, hred⟩ := rootParabolic_exists_reduced_word P b J v hv
  rw [rootWeylLength_mul_reduced_parabolic_word P b J x hx l hl hred]
  exact congrArg (fun n => rootWeylLength P b x + n) hred.symm

/-- Simple-root positivity is exactly minimality throughout the actual right coset. -/
theorem rootWeyl_simple_positive_iff_parabolic_minimal
    (J : Finset b.support) (x : P.weylGroupToPerm.range) :
    (∀ i ∈ J, b.IsPos (x.val i.val)) ↔
      ∀ v ∈ rootParabolicSubgroup P b J,
        rootWeylLength P b x ≤ rootWeylLength P b (x * v) := by
  constructor
  · intro hx v hv
    rw [rootWeylLength_mul_parabolic_of_simple_positive P b J x hx v hv]
    omega
  · intro hmin i hi
    by_contra hneg
    have hs : simpleWeylReflection P b i ∈ rootParabolicSubgroup P b J :=
      Subgroup.subset_closure ⟨i, hi, rfl⟩
    have hle := hmin _ hs
    have hstep := rootWeylLength_mul_simple_of_negative P b x i hneg
    omega

end Atlas.Chevalley.RootData
