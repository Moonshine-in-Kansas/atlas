import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalizerIntersection
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusJoin

/-! The actual join B=U*T intersects the extended Weyl subgroup exactly in T.
This is a consequence of the already specified two-factor decomposition and
U∩N=1; it does not assume any decomposition of the whole Chevalley group. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R] [Fintype κ]

theorem positiveWitnessedTorusJoin_inf_extendedWeyl_eq_torus
    (hdiamond : SimpleDiamondProducts P b) :
    positiveWitnessedTorusJoin P b O hc hm R ⊓
      weightCompanionExtendedWeylSubgroup P b O hc hm R =
      weightCompanionTorusSubgroup P b O hc hm R := by
  apply le_antisymm
  · rintro g ⟨hb, hn⟩
    obtain ⟨p, hp, _⟩ := positiveWitnessedTorusJoin_existsUnique P b O hc hm R hdiamond ⟨g, hb⟩
    change (p.1 : WeightCompanion P b O hc hm R) * p.2 = g at hp
    have htn : (p.2 : WeightCompanion P b O hc hm R) ∈
        weightCompanionExtendedWeylSubgroup P b O hc hm R :=
      weightCompanionTorusSubgroup_le_extendedWeyl P b O hc hm R p.2.property
    have hun : (p.1 : WeightCompanion P b O hc hm R) ∈
        weightCompanionExtendedWeylSubgroup P b O hc hm R := by
      have h := (weightCompanionExtendedWeylSubgroup P b O hc hm R).mul_mem hn
        ((weightCompanionExtendedWeylSubgroup P b O hc hm R).inv_mem htn)
      have he : g * (p.2 : WeightCompanion P b O hc hm R)⁻¹ = p.1 := by
        rw [← hp, mul_inv_cancel_right]
      simpa only [he] using h
    have hu := positiveWitnessedWeightCompanion_eq_one_of_mem_extendedWeyl
      P b O hc hm R hdiamond p.1 p.1.property hun
    have hg : g = (p.2 : WeightCompanion P b O hc hm R) := by
      simpa only [hu, one_mul] using hp.symm
    rw [hg]
    exact p.2.property
  · intro g ht
    exact ⟨(show weightCompanionTorusSubgroup P b O hc hm R ≤
        positiveWitnessedTorusJoin P b O hc hm R from le_sup_right) ht,
      weightCompanionTorusSubgroup_le_extendedWeyl P b O hc hm R ht⟩

end Atlas.Chevalley
