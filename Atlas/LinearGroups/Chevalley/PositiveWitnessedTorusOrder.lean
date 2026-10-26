import Atlas.LinearGroups.Chevalley.PositiveRootCollection
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusJoin

/-! Counting the actual positive-subgroup/torus join from its already proved
internal semidirect product and the collected positive-root coordinates. -/
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
  (R : Type*) [CommRing R] [Nontrivial R] [Finite R] [Fintype κ]

/-- This counts the actual U*T subgroup, without assuming a Bruhat
decomposition or a full-group order. -/
theorem positiveWitnessedTorusJoin_card (hdiamond : SimpleDiamondProducts P b) :
    Nat.card (positiveWitnessedTorusJoin P b O hc hm R) =
      Nat.card R ^ Nat.card {β : ι // b.IsPos β} *
        Nat.card (weightCompanionTorusSubgroup P b O hc hm R) := by
  rw [← Nat.card_congr (positiveWitnessedTorusJoinMulEquiv P b O hc hm R hdiamond).toEquiv,
    SemidirectProduct.card,
    positiveWitnessedWeightCompanionSubgroup_card P b O hc hm R hdiamond]

end Atlas.Chevalley
