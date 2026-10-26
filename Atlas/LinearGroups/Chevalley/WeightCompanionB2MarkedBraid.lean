import Atlas.LinearGroups.Chevalley.WeightCompanionRootMarks
import Atlas.LinearGroups.Chevalley.WeightCompanionB2MarkedLongRoot
import Atlas.LinearGroups.Chevalley.WeightCompanionB2MarkedShortRoot
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidDihedral
import Atlas.LinearGroups.Chevalley.RootData.DihedralRootWords

/-! The four B2 prefix marks agree as labelled, actual subgroups. The two
middle-root identities are proved on all companion blocks before use here;
this file does not assume arbitrary-root coherence or a global kernel theorem. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule Atlas.GroupTheory Atlas.GroupTheory.ReducedWords

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

theorem weightCompanionRootMark_b2_short_middle
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
      (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
        (weightCompanionSimpleRootMark P b O hc hm R i)) =
      labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
        (weightCompanionSimpleRootMark P b O hc hm R i) := by
  apply Prod.ext
  · have hpij : P.pairing i.val j.val = -1 := by
      rw [← P.algebraMap_pairingIn ℤ i.val j.val,
        show P.pairingIn ℤ i.val j.val = -1 from hij]
      simp
    have hpji : P.pairing j.val i.val = -2 := by
      rw [← P.algebraMap_pairingIn ℤ j.val i.val,
        show P.pairingIn ℤ j.val i.val = -2 from hji]
      simp
    change P.reflectionPerm i.val (P.reflectionPerm j.val i.val) =
      P.reflectionPerm j.val i.val
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  · let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    let f := (MulAut.conj nj).toMonoidHom.comp (weightCompanionXHom P b O hc hm R i)
    have h : conjugateSubgroup ni f.range = f.range := by
      apply conjugateSubgroup_range_eq_of_surjective ni f f Inv.inv inv_surjective
      intro x
      exact weightCompanionWeyl_b2_negates_short_conjugate_X
        P b hdiamond O hc hm R i j hne hij hji x.toAdd
    change conjugateSubgroup ni
      (conjugateSubgroup nj (weightCompanionXHom P b O hc hm R i).range) =
        conjugateSubgroup nj (weightCompanionXHom P b O hc hm R i).range
    simpa only [conjugateSubgroup_range, f] using h

theorem weightCompanionRootMark_b2_long_middle
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
      (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
        (weightCompanionSimpleRootMark P b O hc hm R j)) =
      labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
        (weightCompanionSimpleRootMark P b O hc hm R j) := by
  apply Prod.ext
  · have hpij : P.pairing i.val j.val = -1 := by
      rw [← P.algebraMap_pairingIn ℤ i.val j.val,
        show P.pairingIn ℤ i.val j.val = -1 from hij]
      simp
    have hpji : P.pairing j.val i.val = -2 := by
      rw [← P.algebraMap_pairingIn ℤ j.val i.val,
        show P.pairingIn ℤ j.val i.val = -2 from hji]
      simp
    change P.reflectionPerm j.val (P.reflectionPerm i.val j.val) =
      P.reflectionPerm i.val j.val
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  · let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    let f := (MulAut.conj ni).toMonoidHom.comp (weightCompanionXHom P b O hc hm R j)
    have h : conjugateSubgroup nj f.range = f.range := by
      apply conjugateSubgroup_range_eq_of_surjective nj f f id Function.surjective_id
      intro x
      exact weightCompanionWeyl_b2_fixes_long_conjugate_X
        P b hdiamond O hc hm R i j hne hij hji x.toAdd
    change conjugateSubgroup nj
      (conjugateSubgroup ni (weightCompanionXHom P b O hc hm R j).range) =
        conjugateSubgroup ni (weightCompanionXHom P b O hc hm R j).range
    simpa only [conjugateSubgroup_range, f] using h

/-- The B2 local marked braid is an actual equality of sets of pairs, not
merely a comparison of their root-label projections. -/
theorem weightCompanionMarkedWordSet_b2
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    weightCompanionMarkedWordSet P b O hc hm R [i,j,i,j] =
      weightCompanionMarkedWordSet P b O hc hm R [j,i,j,i] := by
  apply markedWordSet_four_of_middle_fixed
    (weightCompanionMarkedWeyl P b O hc hm R) labelledSubgroupAction
    (weightCompanionSimpleRootMark P b O hc hm R) i j
  · exact weightCompanionRootMark_b2_short_middle P b hdiamond O hc hm R i j hne hij hji
  · exact weightCompanionRootMark_b2_long_middle P b hdiamond O hc hm R i j hne hij hji
  · exact weightCompanionSimpleRootMark_weyl_square P b O hc hm R i j
  · exact weightCompanionSimpleRootMark_weyl_square P b O hc hm R j i

omit hdiamond in
theorem weightCompanionMarkedWeyl_b2_braid
    (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    wordEval (weightCompanionMarkedWeyl P b O hc hm R) [i,j,i,j] =
      wordEval (weightCompanionMarkedWeyl P b O hc hm R) [j,i,j,i] := by
  apply Prod.ext
  · simpa only [wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      weightCompanionMarkedWeyl, Prod.fst_mul, Prod.fst_one,
      RootData.reflectionWord, mul_one] using
      RootData.reflectionWord_four P i.val j.val hij hji
  · simpa only [wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      weightCompanionMarkedWeyl, Prod.snd_mul, Prod.snd_one,
      mul_one, mul_assoc] using weightCompanionWeyl_b2_braid P b O hc hm R i j hij hji

/-- Both local obligations needed by marked Matsumoto evaluation have now
been discharged for this double edge: full products and full marks. -/
theorem weightCompanionMarkedLetterEnd_b2_braid
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    wordEval (markedLetterEnd (weightCompanionMarkedWeyl P b O hc hm R)
      labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R)) [i,j,i,j] =
    wordEval (markedLetterEnd (weightCompanionMarkedWeyl P b O hc hm R)
      labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R)) [j,i,j,i] := by
  apply markedLetterEnd_wordEval_eq_of_product_and_marks
  · exact weightCompanionMarkedWeyl_b2_braid P b O hc hm R i j hij hji
  · exact weightCompanionMarkedWordSet_b2 P b hdiamond O hc hm R i j hne hij hji

end Atlas.Chevalley
