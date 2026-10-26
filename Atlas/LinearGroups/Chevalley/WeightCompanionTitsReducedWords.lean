import Atlas.LinearGroups.Chevalley.WeightCompanionNonAdjacentWeyl
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidA2
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylBraidDihedral
import Atlas.LinearGroups.Chevalley.WeightCompanionRootPermutation
import Atlas.LinearGroups.Chevalley.RootData.CommonAlternatingSuffix

/-! Reduced words have the same literal product in the full companion N.
Only actual braid identities are used in the target; the simple Weyl operators
need not be involutions. This does not define a homomorphism from W to N. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData
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

/-- The literal N word is the already constructed full companion word. -/
theorem weightCompanionSimpleWeylInN_wordEval_val (l : List b.support) :
    (wordEval (weightCompanionSimpleWeylInN P b O hc hm R) l).val =
      wordEval (fun i => weightCompanionWeyl P b O hc hm R i 1) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change weightCompanionWeyl P b O hc hm R i 1 *
      (wordEval (weightCompanionSimpleWeylInN P b O hc hm R) l).val =
      weightCompanionWeyl P b O hc hm R i 1 *
        wordEval (fun j => weightCompanionWeyl P b O hc hm R j 1) l
    rw [ih]

/-- Actual full companion braids in the alternating-suffix convention.
The generic diamond premise is used in the zero-edge branch only. -/
theorem weightCompanionWeyl_alternating_braid
    (hdiamond : SimpleDiamondProducts P b) (i j : b.support) (hne : i ≠ j) :
    wordEval (fun k => weightCompanionWeyl P b O hc hm R k 1)
        (alternatingSuffix i j (simpleBraidLength P b i j)) =
      wordEval (fun k => weightCompanionWeyl P b O hc hm R k 1)
        (alternatingSuffix j i (simpleBraidLength P b i j)) := by
  rcases cartanMatrix_pair_cases_of_ne P b i j hne with
    ⟨hij, hji⟩ | ⟨hij, hji⟩ | ⟨hij, hji⟩ |
    ⟨hij, hji⟩ | ⟨hij, hji⟩ | ⟨hij, hji⟩
  · have hlen : simpleBraidLength P b i j = 2 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      (weightCompanionWeyl_commute_of_zero_cartan P b hdiamond O hc hm R
        i j hne hji 1 1).eq.symm
  · have hlen : simpleBraidLength P b i j = 3 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      weightCompanionWeyl_a2_braid P b O hc hm R i j hij hji
  · have hlen : simpleBraidLength P b i j = 4 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      (weightCompanionWeyl_b2_braid P b O hc hm R i j hij hji).symm
  · have hlen : simpleBraidLength P b i j = 4 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      weightCompanionWeyl_b2_braid P b O hc hm R j i hji hij
  · have hlen : simpleBraidLength P b i j = 6 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      (weightCompanionWeyl_g2_braid P b O hc hm R i j hij hji).symm
  · have hlen : simpleBraidLength P b i j = 6 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      weightCompanionWeyl_g2_braid P b O hc hm R j i hji hij

/-- The same braid equality inside the actual subgroup N, before quotienting. -/
theorem weightCompanionSimpleWeylInN_alternating_braid
    (hdiamond : SimpleDiamondProducts P b) (i j : b.support) (hne : i ≠ j) :
    wordEval (weightCompanionSimpleWeylInN P b O hc hm R)
        (alternatingSuffix i j (simpleBraidLength P b i j)) =
      wordEval (weightCompanionSimpleWeylInN P b O hc hm R)
        (alternatingSuffix j i (simpleBraidLength P b i j)) := by
  apply Subtype.ext
  rw [weightCompanionSimpleWeylInN_wordEval_val,
    weightCompanionSimpleWeylInN_wordEval_val]
  exact weightCompanionWeyl_alternating_braid P b O hc hm R hdiamond i j hne

/-- Reduced words for the same actual Weyl permutation have equal products
of the actual full companion Weyl operators. No square relation in N is used. -/
theorem weightCompanionSimpleWeylInN_reduced_wordEval_eq
    (hdiamond : SimpleDiamondProducts P b) {l r : List b.support}
    (hl : IsReducedRootWord P b l) (hr : IsReducedRootWord P b r)
    (heq : rootWeylWord P b l = rootWeylWord P b r) :
    wordEval (weightCompanionSimpleWeylInN P b O hc hm R) l =
      wordEval (weightCompanionSimpleWeylInN P b O hc hm R) r := by
  exact reduced_wordEval_eq_of_alternating (actualRootLengthData P b)
    (weightCompanionSimpleWeylInN P b O hc hm R) (simpleBraidLength P b)
    (fun i j _ => simpleBraidLength_pos P b i j)
    (root_reduced_representatives P b)
    (actualRoot_hasCommonAlternatingSuffix P b)
    (weightCompanionSimpleWeylInN_alternating_braid P b O hc hm R hdiamond)
    hl hr heq

end Atlas.Chevalley
