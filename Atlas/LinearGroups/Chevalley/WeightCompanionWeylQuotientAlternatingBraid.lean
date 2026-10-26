import Atlas.LinearGroups.Chevalley.WeightCompanionWeylQuotientBraids
import Atlas.LinearGroups.Chevalley.RootData.CommonAlternatingSuffix

/-! Adapter from the four literal quotient braid identities to the exact
Cartan-defined alternating-suffix convention used by reduced-word evaluation.
No presentation or faithfulness assumption occurs in this theorem. -/

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

local instance quotientAlternatingBraidTorusNormal :
    ((weightCompanionTorusSubgroup P b O hc hm R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hc hm R)).Normal :=
  weightCompanionTorusSubgroup_normal_extendedWeyl P b O hc hm R

/-- The actual simple cosets obey the exact alternating-suffix identity needed
by the reduced-word theorem. The diamond premise is used only in the zero-edge
branch; actual root-data providers discharge it separately. -/
theorem weightCompanionSimpleWeylCoset_alternating_braid
    (hdiamond : SimpleDiamondProducts P b) (i j : b.support) (hne : i ≠ j) :
    wordEval (weightCompanionSimpleWeylCoset P b O hc hm R)
        (alternatingSuffix i j (simpleBraidLength P b i j)) =
      wordEval (weightCompanionSimpleWeylCoset P b O hc hm R)
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
      (weightCompanionSimpleWeylCoset_commute_of_zero_cartan P b O hc hm R
        hdiamond i j hne hji).eq.symm
  · have hlen : simpleBraidLength P b i j = 3 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      weightCompanionSimpleWeylCoset_a2_braid P b O hc hm R i j hij hji
  · have hlen : simpleBraidLength P b i j = 4 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      (weightCompanionSimpleWeylCoset_b2_braid P b O hc hm R i j hij hji).symm
  · have hlen : simpleBraidLength P b i j = 4 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      weightCompanionSimpleWeylCoset_b2_braid P b O hc hm R j i hji hij
  · have hlen : simpleBraidLength P b i j = 6 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      (weightCompanionSimpleWeylCoset_g2_braid P b O hc hm R i j hij hji).symm
  · have hlen : simpleBraidLength P b i j = 6 := by
      simp [simpleBraidLength, hij, hji]
    rw [hlen]
    simpa only [alternatingSuffix, List.cons_append, List.nil_append,
      wordEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc] using
      weightCompanionSimpleWeylCoset_g2_braid P b O hc hm R j i hji hij

end Atlas.Chevalley
