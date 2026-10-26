import Atlas.LinearGroups.Chevalley.RootData.RationalRootPairPositiveLevi

/-! Every distinct positive-root pair is the actual Weyl image of two
positive roots supported on two simple directions. The transported roots
are not claimed to be the simple roots of that subsystem. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Positive orientation and saturated pair-plane reduction give the precise
local hypothesis needed for full rank-two commutator tables. -/
theorem exists_positive_pair_simple_support
    (α β : {γ : ι // b.IsPos γ}) (hne : α ≠ β) :
    ∃ w : P.weylGroupToPerm.range, ∃ i j : b.support, i ≠ j ∧
      ∃ a c : {γ : ι // b.IsPos γ}, a ≠ c ∧
        w.val a.val = α.val ∧ w.val c.val = β.val ∧
        (rootSimpleCoefficients P b a.val).support ⊆ {i, j} ∧
        (rootSimpleCoefficients P b c.val).support ⊆ {i, j} := by
  have hne' : α.val ≠ β.val := fun h => hne (Subtype.ext h)
  have hneg : P.root α.val ≠ -P.root β.val := by
    intro h
    have he : α.val = P.reflectionPerm β.val β.val := P.root_eq_neg_iff.mp h
    have hh : b.height α.val = -b.height β.val := by
      rw [he]
      exact b.height_reflectionPerm_self β.val
    have ha : 0 < b.height α.val := α.property
    have hb : 0 < b.height β.val := β.property
    omega
  obtain ⟨w, S, hcard, hspan, hs, hp⟩ :=
    exists_rationalRootPair_positive_rankTwoLevi P b α.val β.val hne' hneg
  obtain ⟨i, j, hij, hS⟩ := Finset.card_eq_two.mp hcard
  let a := w.val.symm α.val
  let c := w.val.symm β.val
  have hwa : w.val a = α.val := w.val.apply_symm_apply α.val
  have hwc : w.val c = β.val := w.val.apply_symm_apply β.val
  have haSpan : rationalRootCoordinates P b (w.val a) ∈
      rationalRootPairSpan P b α.val β.val := by
    rw [hwa]
    exact Submodule.subset_span (by simp)
  have hcSpan : rationalRootCoordinates P b (w.val c) ∈
      rationalRootPairSpan P b α.val β.val := by
    rw [hwc]
    exact Submodule.subset_span (by simp)
  have ha : b.IsPos a := (hp a haSpan).mp (by rw [hwa]; exact α.property)
  have hc : b.IsPos c := (hp c hcSpan).mp (by rw [hwc]; exact β.property)
  refine ⟨w, i, j, hij, ⟨a, ha⟩, ⟨c, hc⟩, ?_, hwa, hwc, ?_, ?_⟩
  · intro he
    apply hne'
    calc
      α.val = w.val a := hwa.symm
      _ = w.val c := congrArg w.val (congrArg Subtype.val he)
      _ = β.val := hwc
  · intro k hk
    simpa only [hS] using (hs a).mp haSpan k hk
  · intro k hk
    simpa only [hS] using (hs c).mp hcSpan k hk

end Atlas.Chevalley.RootData
