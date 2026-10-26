import Atlas.GroupTheory.MarkedBraidSix
import Atlas.LinearGroups.Chevalley.WeightCompanionMarkedSquareTransport
import Atlas.LinearGroups.Chevalley.WeightCompanionG2MarkedMiddleRoots
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidDihedral
import Atlas.LinearGroups.Chevalley.RootData.DihedralRootWords
import Mathlib.Tactic.NormNum

/-! The six G2 marked root subgroups. The two middle fixedness identities are
actual full-companion identities. The remaining transport uses exact Weyl
squares and torus scaling, with the negative parameters displayed separately. -/
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

theorem weightCompanionWeyl_g2_sq_short_conjugate_X
    (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (t : R) :
    let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    ni ^ 2 * (nj * weightCompanionX P b O hc hm R i t * nj⁻¹) * (ni ^ 2)⁻¹ =
      nj * weightCompanionX P b O hc hm R i (-t) * nj⁻¹ := by
  have h := weightCompanionWeyl_sq_conjugate_weyl_X P b O hc hm R i j i t
  dsimp only at h ⊢
  have hu : (((-1 : Rˣ) ^ (-b.cartanMatrix j i)) ^ b.cartanMatrix i j *
      (-1) ^ b.cartanMatrix i i) = -1 := by
    norm_num [hij, hji, b.cartanMatrix_apply_same, zpow_neg, zpow_ofNat]
  simpa only [hu, Units.val_neg, Units.val_one, neg_one_mul] using h

theorem weightCompanionWeyl_g2_sq_long_conjugate_X
    (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (t : R) :
    let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    nj ^ 2 * (ni * weightCompanionX P b O hc hm R j t * ni⁻¹) * (nj ^ 2)⁻¹ =
      ni * weightCompanionX P b O hc hm R j (-t) * ni⁻¹ := by
  have h := weightCompanionWeyl_sq_conjugate_weyl_X P b O hc hm R j i j t
  dsimp only at h ⊢
  have hu : (((-1 : Rˣ) ^ (-b.cartanMatrix i j)) ^ b.cartanMatrix j i *
      (-1) ^ b.cartanMatrix j j) = -1 := by
    norm_num [hij, hji, b.cartanMatrix_apply_same, zpow_neg, zpow_ofNat]
  simpa only [hu, Units.val_neg, Units.val_one, neg_one_mul] using h

include hdiamond

theorem weightCompanionRootMark_g2_short_middle
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
      (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
        (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
          (weightCompanionSimpleRootMark P b O hc hm R i))) =
      labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
        (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
          (weightCompanionSimpleRootMark P b O hc hm R i)) := by
  apply Prod.ext
  · have hpij : P.pairing i.val j.val = -1 := by
      rw [← P.algebraMap_pairingIn ℤ i.val j.val,
        show P.pairingIn ℤ i.val j.val = -1 from hij]
      simp
    have hpji : P.pairing j.val i.val = -3 := by
      rw [← P.algebraMap_pairingIn ℤ j.val i.val,
        show P.pairingIn ℤ j.val i.val = -3 from hji]
      simp
    change P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val i.val)) =
      P.reflectionPerm i.val (P.reflectionPerm j.val i.val)
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  · let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    let f := (MulAut.conj (ni * nj)).toMonoidHom.comp
      (weightCompanionXHom P b O hc hm R i)
    have h : conjugateSubgroup nj f.range = f.range := by
      apply conjugateSubgroup_range_eq_of_surjective _ _ _ id Function.surjective_id
      intro x
      exact weightCompanionWeyl_g2_fixes_short_middle_X
        P b hdiamond O hc hm R i j hne hij hji x.toAdd
    change conjugateSubgroup nj (conjugateSubgroup ni
      (conjugateSubgroup nj (weightCompanionXHom P b O hc hm R i).range)) =
        conjugateSubgroup ni
          (conjugateSubgroup nj (weightCompanionXHom P b O hc hm R i).range)
    have hrange : conjugateSubgroup ni
        (conjugateSubgroup nj (weightCompanionXHom P b O hc hm R i).range) = f.range := by
      rw [← conjugateSubgroup_mul]
      exact conjugateSubgroup_range _ _
    simpa only [hrange] using h

theorem weightCompanionRootMark_g2_long_middle
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
      (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
        (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
          (weightCompanionSimpleRootMark P b O hc hm R j))) =
      labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
        (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
          (weightCompanionSimpleRootMark P b O hc hm R j)) := by
  apply Prod.ext
  · have hpij : P.pairing i.val j.val = -1 := by
      rw [← P.algebraMap_pairingIn ℤ i.val j.val,
        show P.pairingIn ℤ i.val j.val = -1 from hij]
      simp
    have hpji : P.pairing j.val i.val = -3 := by
      rw [← P.algebraMap_pairingIn ℤ j.val i.val,
        show P.pairingIn ℤ j.val i.val = -3 from hji]
      simp
    change P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val j.val)) =
      P.reflectionPerm j.val (P.reflectionPerm i.val j.val)
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  · let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    let f := (MulAut.conj (nj * ni)).toMonoidHom.comp
      (weightCompanionXHom P b O hc hm R j)
    have h : conjugateSubgroup ni f.range = f.range := by
      apply conjugateSubgroup_range_eq_of_surjective _ _ _ id Function.surjective_id
      intro x
      exact weightCompanionWeyl_g2_fixes_long_middle_X
        P b hdiamond O hc hm R i j hne hij hji x.toAdd
    change conjugateSubgroup ni (conjugateSubgroup nj
      (conjugateSubgroup ni (weightCompanionXHom P b O hc hm R j).range)) =
        conjugateSubgroup nj
          (conjugateSubgroup ni (weightCompanionXHom P b O hc hm R j).range)
    have hrange : conjugateSubgroup nj
        (conjugateSubgroup ni (weightCompanionXHom P b O hc hm R j).range) = f.range := by
      rw [← conjugateSubgroup_mul]
      exact conjugateSubgroup_range _ _
    simpa only [hrange] using h

theorem weightCompanionMarkedWordSet_g2
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    weightCompanionMarkedWordSet P b O hc hm R [i,j,i,j,i,j] =
      weightCompanionMarkedWordSet P b O hc hm R [j,i,j,i,j,i] := by
  apply markedWordSet_six_of_middle_fixed
    (weightCompanionMarkedWeyl P b O hc hm R) labelledSubgroupAction
    (weightCompanionSimpleRootMark P b O hc hm R) i j
  · exact weightCompanionRootMark_g2_short_middle P b hdiamond O hc hm R i j hne hij hji
  · exact weightCompanionRootMark_g2_long_middle P b hdiamond O hc hm R i j hne hij hji
  · exact weightCompanionSimpleRootMark_weyl_square P b O hc hm R i j
  · exact weightCompanionSimpleRootMark_weyl_square P b O hc hm R j i
  · exact weightCompanionRootMark_weyl_square_conjugate P b O hc hm R i j i
  · exact weightCompanionRootMark_weyl_square_conjugate P b O hc hm R j i j

omit hdiamond in
theorem weightCompanionMarkedWeyl_g2_braid
    (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    wordEval (weightCompanionMarkedWeyl P b O hc hm R) [i,j,i,j,i,j] =
      wordEval (weightCompanionMarkedWeyl P b O hc hm R) [j,i,j,i,j,i] := by
  apply Prod.ext
  · simpa only [wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      weightCompanionMarkedWeyl, Prod.fst_mul, Prod.fst_one,
      RootData.reflectionWord, mul_one] using
      RootData.reflectionWord_six P i.val j.val hij hji
  · simpa only [wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      weightCompanionMarkedWeyl, Prod.snd_mul, Prod.snd_one,
      mul_one, mul_assoc] using weightCompanionWeyl_g2_braid P b O hc hm R i j hij hji

theorem weightCompanionMarkedLetterEnd_g2_braid
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    wordEval (markedLetterEnd (weightCompanionMarkedWeyl P b O hc hm R)
      labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R)) [i,j,i,j,i,j] =
    wordEval (markedLetterEnd (weightCompanionMarkedWeyl P b O hc hm R)
      labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R)) [j,i,j,i,j,i] := by
  apply markedLetterEnd_wordEval_eq_of_product_and_marks
  · exact weightCompanionMarkedWeyl_g2_braid P b O hc hm R i j hij hji
  · exact weightCompanionMarkedWordSet_g2 P b hdiamond O hc hm R i j hne hij hji

end Atlas.Chevalley
