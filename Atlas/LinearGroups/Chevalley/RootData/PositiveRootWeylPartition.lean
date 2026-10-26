import Atlas.LinearGroups.Chevalley.RootData.PositiveRootConeClosed
import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength

/-! The positive roots carried to negative roots by an actual Weyl permutation,
and their complement, are both closed under strict positive integral root cones.
This uses the integral height relation and actual Weyl transport; no constructed
group, group order or Bruhat decomposition enters. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- A strict positive integral combination of two nonpositive root labels
cannot be positive. No division or cancellation in a coefficient field is used. -/
theorem positiveIntegralRootCone_not_isPos {α β γ : ι}
    (h : PositiveIntegralRootCone P b α β γ)
    (hα : ¬ b.IsPos α) (hβ : ¬ b.IsPos β) : ¬ b.IsPos γ := by
  obtain ⟨a, c, ha, hc, he⟩ := (positiveIntegralRootCone_iff_root_eq P b α β γ).mp h
  have hh := root_height_zsmul_add P b α β γ a c he
  rw [b.isPos_iff] at hα hβ ⊢
  apply not_lt_of_ge
  rw [hh]
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg a) (le_of_not_gt hα))
    (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg c) (le_of_not_gt hβ))

/-- Positive labels whose images under the specified actual Weyl permutation
are negative. The direction is w, rather than w⁻¹. -/
def positiveRootInversionSubset (w : P.weylGroupToPerm.range) :
    Set {β : ι // b.IsPos β} :=
  {β | ¬ b.IsPos (w.val β.val)}

/-- Positive labels whose images under the same actual Weyl permutation remain
positive. This is the complement inside the positive-root subtype. -/
def positiveRootNoninversionSubset (w : P.weylGroupToPerm.range) :
    Set {β : ι // b.IsPos β} :=
  {β | b.IsPos (w.val β.val)}

@[simp] theorem mem_positiveRootInversionSubset (w : P.weylGroupToPerm.range)
    (β : {β : ι // b.IsPos β}) :
    β ∈ positiveRootInversionSubset P b w ↔ ¬ b.IsPos (w.val β.val) := Iff.rfl

@[simp] theorem mem_positiveRootNoninversionSubset (w : P.weylGroupToPerm.range)
    (β : {β : ι // b.IsPos β}) :
    β ∈ positiveRootNoninversionSubset P b w ↔ b.IsPos (w.val β.val) := Iff.rfl

theorem positiveRootConeClosed_inversionSubset (w : P.weylGroupToPerm.range) :
    PositiveRootConeClosed P b (positiveRootInversionSubset P b w) := by
  intro α hα β hβ γ hcone
  exact positiveIntegralRootCone_not_isPos P b
    (positiveIntegralRootCone_weyl P b w hcone) hα hβ

theorem positiveRootConeClosed_noninversionSubset (w : P.weylGroupToPerm.range) :
    PositiveRootConeClosed P b (positiveRootNoninversionSubset P b w) := by
  intro α hα β hβ γ hcone
  exact positiveIntegralRootCone_isPos P b
    (positiveIntegralRootCone_weyl P b w hcone) hα hβ

theorem positiveRootInversionSubset_compl (w : P.weylGroupToPerm.range) :
    (positiveRootInversionSubset P b w)ᶜ = positiveRootNoninversionSubset P b w := by
  ext β
  simp only [Set.mem_compl_iff, mem_positiveRootInversionSubset,
    mem_positiveRootNoninversionSubset, not_not]

theorem positiveRootInversionSubset_disjoint (w : P.weylGroupToPerm.range) :
    Disjoint (positiveRootInversionSubset P b w)
      (positiveRootNoninversionSubset P b w) := by
  apply Set.disjoint_left.mpr
  intro β hneg hpos
  exact hneg hpos

theorem positiveRootInversionSubset_union_noninversion (w : P.weylGroupToPerm.range) :
    positiveRootInversionSubset P b w ∪ positiveRootNoninversionSubset P b w = Set.univ := by
  ext β
  simp only [Set.mem_union, mem_positiveRootInversionSubset,
    mem_positiveRootNoninversionSubset, Set.mem_univ, iff_true]
  by_cases h : b.IsPos (w.val β.val)
  · exact Or.inr h
  · exact Or.inl h

theorem positiveRootInversionSubset_inter_noninversion (w : P.weylGroupToPerm.range) :
    positiveRootInversionSubset P b w ∩ positiveRootNoninversionSubset P b w = ∅ := by
  ext β
  simp only [Set.mem_inter_iff, mem_positiveRootInversionSubset,
    mem_positiveRootNoninversionSubset, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hneg, hpos⟩
  exact hneg hpos

/-- This subset is exactly the existing finite inversion set, with positivity
carried by the subtype rather than repeated in the membership predicate. -/
theorem mem_positiveRootInversionSubset_iff_rootInversions
    (w : P.weylGroupToPerm.range) (β : {β : ι // b.IsPos β}) :
    β ∈ positiveRootInversionSubset P b w ↔ β.val ∈ rootInversions P b w := by
  rw [mem_positiveRootInversionSubset, mem_rootInversions]
  exact ⟨fun h => ⟨β.property, h⟩, fun h => h.2⟩

end Atlas.Chevalley.RootData
