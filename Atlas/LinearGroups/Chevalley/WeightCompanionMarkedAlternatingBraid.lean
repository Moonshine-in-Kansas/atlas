import Atlas.LinearGroups.Chevalley.WeightCompanionA2ZeroMarkedBraids
import Atlas.LinearGroups.Chevalley.WeightCompanionB2MarkedBraid
import Atlas.LinearGroups.Chevalley.WeightCompanionG2MarkedBraid
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidA2
import Atlas.LinearGroups.Chevalley.RootData.CommonAlternatingSuffix

/-! Actual local marked braids for all distinct simple pairs. The finite
Cartan-pair theorem selects 2,3,4,6; no bounded-rank enumeration or abstract
Coxeter/presentation assumption is used. Global coherence is not asserted. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule RootData Atlas.GroupTheory Atlas.GroupTheory.ReducedWords
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

private theorem markedWeyl_zero (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = 0) (hji : b.cartanMatrix j i = 0) :
    wordEval (weightCompanionMarkedWeyl P b O hc hm R) [i,j] =
      wordEval (weightCompanionMarkedWeyl P b O hc hm R) [j,i] := by
  apply Prod.ext
  · have h := congrArg Subtype.val (rootWeylWord_braid_two P b i j hij hji)
    simpa only [rootWeylWord_val_eq_reflectionWord, List.map_cons, List.map_nil,
      reflectionWord, wordEval, List.prod_cons, List.prod_nil,
      weightCompanionMarkedWeyl, Prod.fst_mul, Prod.fst_one, mul_one] using h
  · simpa only [wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      weightCompanionMarkedWeyl, Prod.snd_mul, Prod.snd_one, mul_one] using
      (weightCompanionWeyl_commute_of_zero_cartan
        P b hdiamond O hc hm R i j hne hji 1 1).eq

omit hdiamond in
private theorem markedWeyl_a2 (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    wordEval (weightCompanionMarkedWeyl P b O hc hm R) [i,j,i] =
      wordEval (weightCompanionMarkedWeyl P b O hc hm R) [j,i,j] := by
  apply Prod.ext
  · have h := congrArg Subtype.val (rootWeylWord_braid_three P b i j hij hji)
    simpa only [rootWeylWord_val_eq_reflectionWord, List.map_cons, List.map_nil,
      reflectionWord, wordEval, List.prod_cons, List.prod_nil,
      weightCompanionMarkedWeyl, Prod.fst_mul, Prod.fst_one, mul_one] using h
  · simpa only [wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      weightCompanionMarkedWeyl, Prod.snd_mul, Prod.snd_one, mul_one, mul_assoc] using
      weightCompanionWeyl_a2_braid P b O hc hm R i j hij hji

/-- The full paired products obey precisely the alternating convention used
by the existing generic reduced-word theorem. -/
theorem weightCompanionMarkedWeyl_alternating_braid
    (i j : b.support) (hne : i ≠ j) :
    wordEval (weightCompanionMarkedWeyl P b O hc hm R)
        (alternatingSuffix i j (simpleBraidLength P b i j)) =
      wordEval (weightCompanionMarkedWeyl P b O hc hm R)
        (alternatingSuffix j i (simpleBraidLength P b i j)) := by
  rcases cartanMatrix_pair_cases_of_ne P b i j hne with
    ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩
  · have hlen : simpleBraidLength P b i j = 2 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      (markedWeyl_zero P b hdiamond O hc hm R i j hne hij hji).symm
  · have hlen : simpleBraidLength P b i j = 3 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      markedWeyl_a2 P b O hc hm R i j hij hji
  · have hlen : simpleBraidLength P b i j = 4 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      (weightCompanionMarkedWeyl_b2_braid P b O hc hm R i j hij hji).symm
  · have hlen : simpleBraidLength P b i j = 4 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      weightCompanionMarkedWeyl_b2_braid P b O hc hm R j i hji hij
  · have hlen : simpleBraidLength P b i j = 6 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      (weightCompanionMarkedWeyl_g2_braid P b O hc hm R i j hij hji).symm
  · have hlen : simpleBraidLength P b i j = 6 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      weightCompanionMarkedWeyl_g2_braid P b O hc hm R j i hji hij

/-- Every local marked-braid obligation is now an actual labelled-subgroup
identity, with the root-datum diamond premise visible. -/
theorem weightCompanionMarkedWordSet_alternating_braid
    (i j : b.support) (hne : i ≠ j) :
    weightCompanionMarkedWordSet P b O hc hm R
        (alternatingSuffix i j (simpleBraidLength P b i j)) =
      weightCompanionMarkedWordSet P b O hc hm R
        (alternatingSuffix j i (simpleBraidLength P b i j)) := by
  rcases cartanMatrix_pair_cases_of_ne P b i j hne with
    ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩
  · have hlen : simpleBraidLength P b i j = 2 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      (weightCompanionMarkedWordSet_zero P b hdiamond O hc hm R i j hne hij hji).symm
  · have hlen : simpleBraidLength P b i j = 3 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      weightCompanionMarkedWordSet_a2 P b hdiamond O hc hm R i j hne hij hji
  · have hlen : simpleBraidLength P b i j = 4 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      (weightCompanionMarkedWordSet_b2 P b hdiamond O hc hm R i j hne hij hji).symm
  · have hlen : simpleBraidLength P b i j = 4 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      weightCompanionMarkedWordSet_b2 P b hdiamond O hc hm R j i hne.symm hji hij
  · have hlen : simpleBraidLength P b i j = 6 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      (weightCompanionMarkedWordSet_g2 P b hdiamond O hc hm R i j hne hij hji).symm
  · have hlen : simpleBraidLength P b i j = 6 := by simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append] using
      weightCompanionMarkedWordSet_g2 P b hdiamond O hc hm R j i hne.symm hji hij

/-- The exact set-endomorphism braid, combining the independent product and
marked-set obligations. This does not yet assert global witness coherence. -/
theorem weightCompanionMarkedLetterEnd_alternating_braid
    (i j : b.support) (hne : i ≠ j) :
    wordEval (markedLetterEnd (weightCompanionMarkedWeyl P b O hc hm R)
      labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R))
        (alternatingSuffix i j (simpleBraidLength P b i j)) =
    wordEval (markedLetterEnd (weightCompanionMarkedWeyl P b O hc hm R)
      labelledSubgroupAction (weightCompanionSimpleRootMark P b O hc hm R))
        (alternatingSuffix j i (simpleBraidLength P b i j)) := by
  apply markedLetterEnd_wordEval_eq_of_product_and_marks
  · exact weightCompanionMarkedWeyl_alternating_braid P b hdiamond O hc hm R i j hne
  · exact weightCompanionMarkedWordSet_alternating_braid P b hdiamond O hc hm R i j hne

end Atlas.Chevalley
