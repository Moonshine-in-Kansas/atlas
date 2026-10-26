import Atlas.LinearGroups.Chevalley.RootData.RationalRootPairPositiveLevi
import Atlas.LinearGroups.Chevalley.RootData.RootWordLabels
import Atlas.LinearGroups.Chevalley.RootData.RootInversionLength

/-! Root support and exhaustive labels of a reduced word negating its support.
This is actual root combinatorics, with no group root-subgroup assumptions. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- A simple reflection changes only its own actual simple coefficient. -/
theorem rootSimpleCoefficients_reflection (i : b.support) (β : ι) :
    rootSimpleCoefficients P b (P.reflectionPerm i.val β) =
      rootSimpleCoefficients P b β -
        (P.pairingIn ℤ β i.val) • Finsupp.single i 1 := by
  have hr : P.rootSpanMem ℤ (P.reflectionPerm i.val β) =
      P.rootSpanMem ℤ β - (P.pairingIn ℤ β i.val) • P.rootSpanMem ℤ i.val := by
    apply Subtype.ext
    change P.root (P.reflectionPerm i.val β) =
      P.root β - (P.pairingIn ℤ β i.val) • P.root i.val
    rw [P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing,
      ← P.algebraMap_pairingIn ℤ β i.val]
    simp
  change b.toWeightBasisInt.repr (P.rootSpanMem ℤ (P.reflectionPerm i.val β)) = _
  rw [hr, map_sub, map_smul]
  change rootSimpleCoefficients P b β - (P.pairingIn ℤ β i.val) •
    rootSimpleCoefficients P b i.val = _
  rw [rootSimpleCoefficients_simple]

theorem rootSimpleCoefficients_reflection_support_subset
    (S : Finset b.support) (i : b.support) (hi : i ∈ S) (β : ι)
    (hβ : (rootSimpleCoefficients P b β).support ⊆ S) :
    (rootSimpleCoefficients P b (P.reflectionPerm i.val β)).support ⊆ S := by
  intro k hk
  by_contra hkS
  have hkβ : rootSimpleCoefficients P b β k = 0 := by
    by_contra hn
    exact hkS (hβ (Finsupp.mem_support_iff.mpr hn))
  have hik : i ≠ k := by
    intro he
    exact hkS (he ▸ hi)
  have hz : rootSimpleCoefficients P b (P.reflectionPerm i.val β) k = 0 := by
    simp only [rootSimpleCoefficients_reflection, Finsupp.sub_apply,
      Finsupp.smul_apply, Finsupp.single_apply, ite_eq_right hik, smul_zero, sub_zero, hkβ]
  exact (Finsupp.mem_support_iff.mp hk) hz

/-- Every label of a word supported on S is itself supported on S. -/
theorem rootWordLabels_support_subset (S : Finset b.support)
    (l : List b.support) (hl : ∀ i ∈ l, i ∈ S) {β : ι}
    (hβ : β ∈ rootWordLabels P b l) :
    (rootSimpleCoefficients P b β).support ⊆ S := by
  induction l generalizing β with
  | nil => exact False.elim (List.not_mem_nil hβ)
  | cons i l ih =>
    rcases List.mem_cons.mp hβ with heq | htail
    · subst β
      rw [rootSimpleCoefficients_simple, Finsupp.support_single i (by decide : (1 : ℤ) ≠ 0)]
      exact Finset.singleton_subset_iff.mpr (hl i (List.mem_cons_self))
    · obtain ⟨γ, hγ, hγβ⟩ := List.mem_map.mp htail
      rw [← hγβ]
      exact rootSimpleCoefficients_reflection_support_subset P b S i
        (hl i List.mem_cons_self) γ
        (ih (fun k hk => hl k (List.mem_cons_of_mem i hk)) hγ)

/-- If every simple direction in S has negative image, so does every
positive root with support contained in S. -/
theorem rootWeyl_not_isPos_of_simple_support
    (S : Finset b.support) (w : P.weylGroupToPerm.range)
    (hw : ∀ i ∈ S, ¬ b.IsPos (w.val i.val))
    {β : ι} (hβ : b.IsPos β) (hs : (rootSimpleCoefficients P b β).support ⊆ S) :
    ¬ b.IsPos (w.val β) := by
  let f := ((Pi.basisFun ℚ b.support).sumCoords.comp
    (rationalRootWeylEquiv P b w).toLinearMap).toAddMonoidHom.comp
      (rationalRootSpanMap P b).toAddMonoidHom
  have hsum : (b.height (w.val β) : ℚ) =
      ∑ i : b.support, (rootSimpleCoefficients P b β i : ℚ) *
        (b.height (w.val i.val) : ℚ) := by
    have he := rootSimpleCoefficients_functional_sum P b f β
    change (Pi.basisFun ℚ b.support).sumCoords
      ((rationalRootWeylEquiv P b w).toLinearMap (rationalRootCoordinates P b β)) =
      ∑ i : b.support, (rootSimpleCoefficients P b β i : ℚ) *
        (Pi.basisFun ℚ b.support).sumCoords
          ((rationalRootWeylEquiv P b w).toLinearMap
            (rationalRootCoordinates P b i.val)) at he
    simpa only [LinearEquiv.coe_coe, rationalRootWeylEquiv_root,
      rationalRootCoordinates_sumCoords] using he
  have hn : (b.height (w.val β) : ℚ) ≤ 0 := by
    rw [hsum]
    apply Finset.sum_nonpos
    intro i hi
    by_cases hc : rootSimpleCoefficients P b β i = 0
    · rw [hc, Int.cast_zero, zero_mul]
    · have hiS := hs (Finsupp.mem_support_iff.mpr hc)
      have hi0 : b.height (w.val i.val) ≤ 0 := le_of_not_gt (hw i hiS)
      exact mul_nonpos_of_nonneg_of_nonpos
        (Int.cast_nonneg (rootSimpleCoefficients_nonneg P b hβ i))
        (Int.cast_nonpos.mpr hi0)
  intro hp
  exact (not_lt_of_ge hn) (Int.cast_pos.mpr hp)

/-- A reduced word using S and negating every simple direction in S
exhausts every positive root supported on S. This also proves there are no
unlisted roots in a two-simple support when applied to the literal braids. -/
theorem rootWordLabels_toFinset_eq_positive_supported
    (S : Finset b.support) (l : List b.support)
    (hl : ∀ i ∈ l, i ∈ S) (hred : IsReducedRootWord P b l)
    (hneg : ∀ i ∈ S, ¬ b.IsPos ((rootWeylWord P b l).val i.val)) :
    (rootWordLabels P b l).toFinset =
      Finset.univ.filter (fun β : ι =>
        b.IsPos β ∧ (rootSimpleCoefficients P b β).support ⊆ S) := by
  let T := Finset.univ.filter (fun β : ι =>
    b.IsPos β ∧ (rootSimpleCoefficients P b β).support ⊆ S)
  have hsub : (rootWordLabels P b l).toFinset ⊆ T := by
    intro β hβ
    have hm := List.mem_toFinset.mp hβ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ β,
      isReducedRootWord_labels_positive P b l hred hm,
      rootWordLabels_support_subset P b S l hl hm⟩
  have hinv : T ⊆ rootInversions P b (rootWeylWord P b l) := by
    intro β hβ
    obtain ⟨_, hp, hs⟩ := Finset.mem_filter.mp hβ
    exact (mem_rootInversions P b _ β).mpr ⟨hp,
      rootWeyl_not_isPos_of_simple_support P b S _ hneg hp hs⟩
  have hcard : T.card ≤ (rootWordLabels P b l).toFinset.card := by
    calc
      T.card ≤ (rootInversions P b (rootWeylWord P b l)).card := Finset.card_le_card hinv
      _ = rootWeylLength P b (rootWeylWord P b l) :=
        rootInversionCount_eq_rootWeylLength P b _
      _ = l.length := hred
      _ = (rootWordLabels P b l).toFinset.card := by
        rw [List.toFinset_card_of_nodup (isReducedRootWord_labels_nodup P b l hred),
          rootWordLabels_length]
  exact Finset.eq_of_subset_of_card_le hsub hcard

theorem rootWordLabels_mem_iff_positive_supported
    (S : Finset b.support) (l : List b.support)
    (hl : ∀ i ∈ l, i ∈ S) (hred : IsReducedRootWord P b l)
    (hneg : ∀ i ∈ S, ¬ b.IsPos ((rootWeylWord P b l).val i.val)) (β : ι) :
    β ∈ rootWordLabels P b l ↔
      b.IsPos β ∧ (rootSimpleCoefficients P b β).support ⊆ S := by
  rw [← List.mem_toFinset,
    rootWordLabels_toFinset_eq_positive_supported P b S l hl hred hneg]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Atlas.Chevalley.RootData
