import Atlas.LinearGroups.Chevalley.SmallRankPositiveConeContainment
import Atlas.LinearGroups.Chevalley.G2PositiveConeContainment
import Atlas.LinearGroups.Chevalley.RootData.RankTwoRootWordEnumeration
import Atlas.LinearGroups.Chevalley.RootData.RankTwoLiteralRootLists
import Mathlib.Tactic.Tauto

/-! Exhaustive Cartan-case dispatch of actual local root-subgroup tables.
The two input roots may be any positive roots supported on the same simple
pair; they are not assumed to be that simple pair themselves. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData
open scoped commutatorElement
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]
  (hdiamond : SimpleDiamondProducts P b)
include hdiamond

/-- Every distinct positive pair supported in two distinct actual simple
directions satisfies the original-pair cone containment. This is the exact
local premise consumed by the global positive-pair reduction. -/
theorem positiveRootSubgroup_two_simple_support_cone
    (i j : b.support) (hne : i ≠ j)
    (α β : {γ : ι // b.IsPos γ}) (_hne : α ≠ β)
    (hα : (rootSimpleCoefficients P b α.val).support ⊆ {i,j})
    (hβ : (rootSimpleCoefficients P b β.val).support ⊆ {i,j}) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
  have htwo (a c : b.support) (hne : a ≠ c)
      (hac : b.cartanMatrix a c = 0) (hca : b.cartanMatrix c a = 0)
      (ha : (rootSimpleCoefficients P b α.val).support ⊆ {a,c})
      (hb : (rootSimpleCoefficients P b β.val).support ⊆ {a,c}) :
      ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
        positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
        positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
    have hlist (γ : {γ : ι // b.IsPos γ})
        (hγ : (rootSimpleCoefficients P b γ.val).support ⊆ {a,c}) :
        γ.val = a.val ∨ γ.val = c.val := by
      have h := (rankTwo_rootWordLabels_two P b a c hac hca).2 γ.val
      have hm := h.mpr ⟨γ.property,hγ⟩
      simpa only [rootWordLabels_two_literal P b a c hca,
        List.mem_cons,List.not_mem_nil,or_false] using hm
    exact positiveRootSubgroup_a1xa1_local_cone P b O hc hm R hdiamond
      a c hne hac hca α β (hlist α ha) (hlist β hb)
  have hthree (a c : b.support) (hne : a ≠ c)
      (hac : b.cartanMatrix a c = -1) (hca : b.cartanMatrix c a = -1)
      (ha : (rootSimpleCoefficients P b α.val).support ⊆ {a,c})
      (hb : (rootSimpleCoefficients P b β.val).support ⊆ {a,c}) :
      ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
        positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
        positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
    have hlist (γ : {γ : ι // b.IsPos γ})
        (hγ : (rootSimpleCoefficients P b γ.val).support ⊆ {a,c}) :
        γ.val = a.val ∨ γ.val = c.val ∨ γ.val = P.reflectionPerm a.val c.val := by
      have hm := ((rankTwo_rootWordLabels_three P b a c hac hca).2 γ.val).mpr ⟨γ.property,hγ⟩
      simp only [rootWordLabels_three_literal P b a c hac hca,
        List.mem_cons,List.not_mem_nil,or_false] at hm
      tauto
    exact positiveRootSubgroup_a2_local_cone P b O hc hm R hdiamond
      a c hne hac hca α β (hlist α ha) (hlist β hb)
  have hfour (a c : b.support) (hne : a ≠ c)
      (hac : b.cartanMatrix a c = -1) (hca : b.cartanMatrix c a = -2)
      (ha : (rootSimpleCoefficients P b α.val).support ⊆ {a,c})
      (hb : (rootSimpleCoefficients P b β.val).support ⊆ {a,c}) :
      ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
        positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
        positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
    have hlist (γ : {γ : ι // b.IsPos γ})
        (hγ : (rootSimpleCoefficients P b γ.val).support ⊆ {a,c}) :
        γ.val = a.val ∨ γ.val = c.val ∨ γ.val = P.reflectionPerm c.val a.val ∨
          γ.val = P.reflectionPerm a.val c.val := by
      have hm := ((rankTwo_rootWordLabels_four P b a c hac hca).2 γ.val).mpr ⟨γ.property,hγ⟩
      simp only [rootWordLabels_four_literal P b a c hac hca,
        List.mem_cons,List.not_mem_nil,or_false] at hm
      tauto
    exact positiveRootSubgroup_b2_local_cone P b O hc hm R hdiamond
      a c hne hac hca α β (hlist α ha) (hlist β hb)
  have hsix (a c : b.support) (hne : a ≠ c)
      (hac : b.cartanMatrix a c = -1) (hca : b.cartanMatrix c a = -3)
      (ha : (rootSimpleCoefficients P b α.val).support ⊆ {a,c})
      (hb : (rootSimpleCoefficients P b β.val).support ⊆ {a,c}) :
      ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
        positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
        positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
    have hlist (γ : {γ : ι // b.IsPos γ})
        (hγ : (rootSimpleCoefficients P b γ.val).support ⊆ {a,c}) :
        γ.val = a.val ∨ γ.val = c.val ∨ γ.val = P.reflectionPerm c.val a.val ∨
          γ.val = P.reflectionPerm a.val (P.reflectionPerm c.val a.val) ∨
          γ.val = P.reflectionPerm a.val c.val ∨
          γ.val = P.reflectionPerm c.val (P.reflectionPerm a.val c.val) := by
      have hm := ((rankTwo_rootWordLabels_six P b a c hac hca).2 γ.val).mpr ⟨γ.property,hγ⟩
      simp only [rootWordLabels_six_literal P b a c hac hca,
        List.mem_cons,List.not_mem_nil,or_false] at hm
      tauto
    exact positiveRootSubgroup_g2_local_cone P b O hc hm R hdiamond
      a c hne hac hca α β (hlist α ha) (hlist β hb)
  rcases cartanMatrix_pair_cases_of_ne P b i j hne with
    ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩ | ⟨hij,hji⟩
  · exact htwo i j hne hij hji hα hβ
  · exact hthree i j hne hij hji hα hβ
  · exact hfour i j hne hij hji hα hβ
  · exact hfour j i hne.symm hji hij
      (by simpa only [Finset.pair_comm] using hα) (by simpa only [Finset.pair_comm] using hβ)
  · exact hsix i j hne hij hji hα hβ
  · exact hsix j i hne.symm hji hij
      (by simpa only [Finset.pair_comm] using hα) (by simpa only [Finset.pair_comm] using hβ)

end Atlas.Chevalley
