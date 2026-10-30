import Atlas.LinearGroups.Chevalley.TwistedE6.WeightedRootInversions
import Atlas.LinearGroups.Chevalley.RootData.ParabolicCosetDecomposition
import Mathlib.Data.Fintype.BigOperators

/-! Weighted inversion sums in the actual right-parabolic coordinates.
The weights are invariant under simple reflections. Reduced words establish
additivity; no evaluation of a Weyl sum or group-order formula is assumed. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.WeightedParabolicFactor
open Classical RootData WeightedRootInversions

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (μ : ι → ℕ)

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

/-- No cancellation occurs when a minimal right-coset representative is
followed by a reduced word in the parabolic generators. Each letter contributes
its actual root weight. -/
theorem weightedInversions_mul_reduced_parabolic_word
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (J : Finset b.support) (x : P.weylGroupToPerm.range)
    (hx : ∀ i ∈ J, b.IsPos (x.val i.val))
    (l : List b.support) (hl : ∀ i ∈ l, i ∈ J)
    (hred : IsReducedRootWord P b l) :
    weightedInversions P b μ (x * rootWeylWord P b l) =
      weightedInversions P b μ x + (l.map (fun i => μ i.val)).sum := by
  induction l using List.reverseRecOn with
  | nil => simp only [rootWeylWord, List.map_nil, List.prod_nil, mul_one,
      List.sum_nil, Nat.add_zero]
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
    have hstep := weightedInversions_mul_simple_of_positive P b μ hμ
      (x * rootWeylWord P b l) i hpos
    have hword : x * rootWeylWord P b (l ++ [i]) =
        (x * rootWeylWord P b l) * simpleWeylReflection P b i := by
      rw [word_append_simple, mul_assoc]
    rw [hword, hstep, ih hlJ hlred]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc]

/-- Any reduced word computes the weighted inversion statistic. -/
theorem weightedInversions_reduced_word
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (l : List b.support) (hred : IsReducedRootWord P b l) :
    weightedInversions P b μ (rootWeylWord P b l) =
      (l.map (fun i => μ i.val)).sum := by
  have h := weightedInversions_mul_reduced_parabolic_word P b μ hμ Finset.univ 1
    (fun i _ => b.isPos_of_mem_support i.property) l
    (fun i _ => Finset.mem_univ i) hred
  simpa only [one_mul, weightedInversions_one, Nat.zero_add] using h

/-- Weighted length is additive in the actual minimal/parabolic factorization. -/
theorem weightedInversions_mul_parabolic_of_simple_positive
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (J : Finset b.support) (x : P.weylGroupToPerm.range)
    (hx : ∀ i ∈ J, b.IsPos (x.val i.val))
    (v : P.weylGroupToPerm.range) (hv : v ∈ rootParabolicSubgroup P b J) :
    weightedInversions P b μ (x * v) =
      weightedInversions P b μ x + weightedInversions P b μ v := by
  obtain ⟨l, hl, rfl, hred⟩ := rootParabolic_exists_reduced_word P b J v hv
  rw [weightedInversions_mul_reduced_parabolic_word P b μ hμ J x hx l hl hred,
    weightedInversions_reduced_word P b μ hμ l hred]

theorem rootParabolicProductEquiv_weightedInversions
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (J : Finset b.support)
    (p : rootParabolicRepresentatives P b J × rootParabolicSubgroup P b J) :
    weightedInversions P b μ (rootParabolicProductEquiv P b J p) =
      weightedInversions P b μ p.1.val + weightedInversions P b μ p.2.val :=
  weightedInversions_mul_parabolic_of_simple_positive P b μ hμ J
    p.1.val p.1.property p.2.val p.2.property

local instance : Fintype P.weylGroupToPerm.range := Fintype.ofFinite _
local instance (J : Finset b.support) : Fintype (rootParabolicRepresentatives P b J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance (J : Finset b.support) : Fintype (rootParabolicSubgroup P b J) :=
  Fintype.ofFinite _

/-- Factorization of the actual weighted sum; neither factor is evaluated here. -/
theorem weightedWeylSum_parabolic_factor
    (hμ : ∀ i : b.support, ∀ β : ι, μ (P.reflectionPerm i.val β) = μ β)
    (J : Finset b.support) (q : ℕ) :
    (∑ w : P.weylGroupToPerm.range, q ^ weightedInversions P b μ w) =
      (∑ x : rootParabolicRepresentatives P b J, q ^ weightedInversions P b μ x.val) *
        (∑ v : rootParabolicSubgroup P b J, q ^ weightedInversions P b μ v.val) := by
  calc
    _ = ∑ p : rootParabolicRepresentatives P b J × rootParabolicSubgroup P b J,
        q ^ weightedInversions P b μ (rootParabolicProductEquiv P b J p) :=
      ((rootParabolicProductEquiv P b J).sum_comp
        (fun w => q ^ weightedInversions P b μ w)).symm
    _ = ∑ p : rootParabolicRepresentatives P b J × rootParabolicSubgroup P b J,
        q ^ weightedInversions P b μ p.1.val * q ^ weightedInversions P b μ p.2.val := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [rootParabolicProductEquiv_weightedInversions P b μ hμ, pow_add]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

end Atlas.Chevalley.TwistedE6.WeightedParabolicFactor
