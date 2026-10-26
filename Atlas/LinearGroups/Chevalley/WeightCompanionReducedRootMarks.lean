import Atlas.GroupTheory.MarkedWordLabelUniqueness
import Atlas.LinearGroups.Chevalley.WeightCompanionMarkedAlternatingBraid
import Atlas.LinearGroups.Chevalley.RootData.LongestRootLabels
import Atlas.LinearGroups.Chevalley.RootData.RootWeylLongestExtension
import Atlas.LinearGroups.Chevalley.WeightCompanionTitsLift

/-! Actual positive-root subgroups from reduced prefix witnesses.
Local marked braids, label injectivity and longest extensions have distinct
roles. No global adjoint injectivity or arbitrary-lift coherence is assumed. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
open Atlas.GroupTheory.ReducedWords
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- The ordered actual paired marks have exactly the checked root-label list. -/
theorem weightCompanionMarkedWordList_fst (l : List b.support) :
    (markedWordList (weightCompanionMarkedWeyl P b O hc hm R)
      labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R) l).map
        Prod.fst = rootWordLabels P b l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [markedWordList, List.map_cons, rootWordLabels]
    erw [List.map_map]
    change i.val :: List.map (fun m => (P.reflectionPerm i.val) m.1)
      (markedWordList (weightCompanionMarkedWeyl P b O hc hm R)
        labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R) l) =
      i.val :: List.map (P.reflectionPerm i.val) (rootWordLabels P b l)
    rw [← ih, List.map_map]
    rfl

/-- A reduced word contains at most one actual subgroup at each root label. -/
theorem weightCompanionMarkedWordSet_label_injective (l : List b.support)
    (hred : IsReducedRootWord P b l)
    {x y : ι × Subgroup (WeightCompanion P b O hc hm R)}
    (hx : x ∈ weightCompanionMarkedWordSet P b O hc hm R l)
    (hy : y ∈ weightCompanionMarkedWordSet P b O hc hm R l)
    (hxy : x.1 = y.1) : x = y := by
  let L := markedWordList (weightCompanionMarkedWeyl P b O hc hm R)
    labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R) l
  have hn : (L.map Prod.fst).Nodup := by
    dsimp only [L]
    rw [weightCompanionMarkedWordList_fst]
    exact isReducedRootWord_labels_nodup P b l hred
  apply eq_of_mem_of_nodup_labels Prod.fst L hn
  · exact (mem_markedWordList_iff _ _ _ l x).mpr hx
  · exact (mem_markedWordList_iff _ _ _ l y).mpr hy
  · exact hxy

/-- Every positive root has exactly one subgroup mark in any reduced longest word. -/
theorem weightCompanionMarkedWordSet_longest_existsUnique (l : List b.support)
    (hred : IsReducedRootWord P b l)
    (hw : rootWeylWord P b l = rootWeylLongest P b) {β : ι} (hβ : b.IsPos β) :
    ∃! H : Subgroup (WeightCompanion P b O hc hm R),
      (β,H) ∈ weightCompanionMarkedWordSet P b O hc hm R l := by
  let L := markedWordList (weightCompanionMarkedWeyl P b O hc hm R)
    labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R) l
  have hn : (L.map Prod.fst).Nodup := by
    dsimp only [L]
    rw [weightCompanionMarkedWordList_fst]
    exact isReducedRootWord_labels_nodup P b l hred
  have hb : β ∈ L.map Prod.fst := by
    dsimp only [L]
    rw [weightCompanionMarkedWordList_fst]
    exact (rootWordLabels_longest_mem_iff P b l hred hw β).mpr hβ
  obtain ⟨H, hH, huniq⟩ := existsUnique_value_of_mem_nodup_labels L hn hb
  refine ⟨H, (mem_markedWordList_iff _ _ _ l (β,H)).mp hH, ?_⟩
  intro K hK
  exact huniq K ((mem_markedWordList_iff _ _ _ l (β,K)).mpr hK)

/-- Local actual marked braids give equality of full paired-mark sets for
reduced expressions of the same actual Weyl element. -/
theorem weightCompanionMarkedWordSet_reduced_eq
    (hdiamond : SimpleDiamondProducts P b) {l r : List b.support}
    (hl : IsReducedRootWord P b l) (hr : IsReducedRootWord P b r)
    (heq : rootWeylWord P b l = rootWeylWord P b r) :
    weightCompanionMarkedWordSet P b O hc hm R l =
      weightCompanionMarkedWordSet P b O hc hm R r := by
  exact reduced_markedWordSet_eq_of_alternating (actualRootLengthData P b)
    (weightCompanionMarkedWeyl P b O hc hm R) labelledSubgroupAction
    (weightCompanionSimpleRootMark P b O hc hm R) (simpleBraidLength P b)
    (fun i j _ => simpleBraidLength_pos P b i j)
    (root_reduced_representatives P b) (actualRoot_hasCommonAlternatingSuffix P b)
    (weightCompanionMarkedWeyl_alternating_braid P b hdiamond O hc hm R)
    (weightCompanionMarkedWordSet_alternating_braid P b hdiamond O hc hm R)
    hl hr heq

theorem weightCompanionMarkedWeyl_wordEval_fst (l : List b.support) :
    (wordEval (weightCompanionMarkedWeyl P b O hc hm R) l).1 =
      (rootWeylWord P b l).val := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change P.reflectionPerm i.val *
      (wordEval (weightCompanionMarkedWeyl P b O hc hm R) l).1 =
      P.reflectionPerm i.val * (rootWeylWord P b l).val
    rw [ih]

theorem weightCompanionMarkedWeyl_wordEval_snd (l : List b.support) :
    (wordEval (weightCompanionMarkedWeyl P b O hc hm R) l).2 =
      wordEval (fun i => weightCompanionWeyl P b O hc hm R i 1) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change weightCompanionWeyl P b O hc hm R i 1 *
      (wordEval (weightCompanionMarkedWeyl P b O hc hm R) l).2 =
      weightCompanionWeyl P b O hc hm R i 1 *
        wordEval (fun j => weightCompanionWeyl P b O hc hm R j 1) l
    rw [ih]

/-- Two reduced prefixes producing the same positive label produce the same
literal subgroup inside the full weight companion. -/
theorem weightCompanion_reducedPrefix_rootSubgroup_eq
    (hdiamond : SimpleDiamondProducts P b)
    (p q : List b.support) (hp : IsReducedRootWord P b p) (hq : IsReducedRootWord P b q)
    (i j : b.support) (hpos : b.IsPos ((rootWeylWord P b p).val i.val))
    (hlabel : (rootWeylWord P b p).val i.val = (rootWeylWord P b q).val j.val) :
    conjugateSubgroup (wordEval (fun k => weightCompanionWeyl P b O hc hm R k 1) p)
      (weightCompanionXHom P b O hc hm R i).range =
    conjugateSubgroup (wordEval (fun k => weightCompanionWeyl P b O hc hm R k 1) q)
      (weightCompanionXHom P b O hc hm R j).range := by
  obtain ⟨p', hpw, hpred⟩ := exists_reduced_marked_extension P b p hp i hpos
  obtain ⟨q', hqw, hqred⟩ := exists_reduced_marked_extension P b q hq j
    (by rw [← hlabel]; exact hpos)
  let x := labelledSubgroupAction (wordEval (weightCompanionMarkedWeyl P b O hc hm R) p)
    (weightCompanionSimpleRootMark P b O hc hm R i)
  let y := labelledSubgroupAction (wordEval (weightCompanionMarkedWeyl P b O hc hm R) q)
    (weightCompanionSimpleRootMark P b O hc hm R j)
  have hx : x ∈ weightCompanionMarkedWordSet P b O hc hm R (p ++ i :: p') :=
    prefix_mark_mem_markedWordSet _ _ _ p p' i
  have hy : y ∈ weightCompanionMarkedWordSet P b O hc hm R (q ++ j :: q') :=
    prefix_mark_mem_markedWordSet _ _ _ q q' j
  have heq := weightCompanionMarkedWordSet_reduced_eq P b O hc hm R hdiamond
    hpred hqred (hpw.trans hqw.symm)
  rw [← heq] at hy
  have hxy : x.1 = y.1 := by
    change (wordEval (weightCompanionMarkedWeyl P b O hc hm R) p).1 i.val =
      (wordEval (weightCompanionMarkedWeyl P b O hc hm R) q).1 j.val
    rw [weightCompanionMarkedWeyl_wordEval_fst, weightCompanionMarkedWeyl_wordEval_fst]
    exact hlabel
  have h := congrArg Prod.snd
    (weightCompanionMarkedWordSet_label_injective P b O hc hm R _ hpred hx hy hxy)
  change conjugateSubgroup (wordEval (weightCompanionMarkedWeyl P b O hc hm R) p).2
      (weightCompanionXHom P b O hc hm R i).range =
    conjugateSubgroup (wordEval (weightCompanionMarkedWeyl P b O hc hm R) q).2
      (weightCompanionXHom P b O hc hm R j).range at h
  simpa only [weightCompanionMarkedWeyl_wordEval_snd] using h

/-- Canonical Tits representatives have coherent positive-root subgroups even
when both the initial simple root and the Weyl permutation vary. -/
theorem weightCompanionTitsLift_positive_rootSubgroup_eq
    (hdiamond : SimpleDiamondProducts P b) (w v : P.weylGroupToPerm.range)
    (i j : b.support) (hpos : b.IsPos (w.val i.val))
    (hlabel : w.val i.val = v.val j.val) :
    conjugateSubgroup (weightCompanionTitsLift P b O hc hm R w).val
      (weightCompanionXHom P b O hc hm R i).range =
    conjugateSubgroup (weightCompanionTitsLift P b O hc hm R v).val
      (weightCompanionXHom P b O hc hm R j).range := by
  obtain ⟨p, hp, hplen⟩ := root_reduced_representatives P b w
  obtain ⟨q, hq, hqlen⟩ := root_reduced_representatives P b v
  change rootWeylWord P b p = w at hp
  change rootWeylWord P b q = v at hq
  have hpred : IsReducedRootWord P b p := by
    change rootWeylLength P b (rootWeylWord P b p) = p.length
    rw [hp, hplen]
  have hqred : IsReducedRootWord P b q := by
    change rootWeylLength P b (rootWeylWord P b q) = q.length
    rw [hq, hqlen]
  rw [weightCompanionTitsLift_eq_wordEval P b O hc hm R hdiamond w p hp hpred,
    weightCompanionTitsLift_eq_wordEval P b O hc hm R hdiamond v q hq hqred,
    weightCompanionSimpleWeylInN_wordEval_val, weightCompanionSimpleWeylInN_wordEval_val]
  apply weightCompanion_reducedPrefix_rootSubgroup_eq P b O hc hm R hdiamond p q hpred hqred i j
  · simpa only [hp] using hpos
  · simpa only [hp, hq] using hlabel

end Atlas.Chevalley
