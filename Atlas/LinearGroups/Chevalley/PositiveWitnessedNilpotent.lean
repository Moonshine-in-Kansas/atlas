import Atlas.LinearGroups.Chevalley.PositiveRootCollection
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Nilpotent

/-! The actual collected positive subgroup over a finite field is a group
of characteristic-prime-power order, hence nilpotent and solvable.
No full-group order, simplicity, or finite orbit-index family is used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K] [Finite K]
  (hdiamond : SimpleDiamondProducts P b)

include hdiamond

theorem positiveWitnessedWeightCompanionSubgroup_isPGroup
    (p : ℕ) [CharP K p] :
    IsPGroup p (positiveWitnessedWeightCompanionSubgroup P b O hc hm K) := by
  letI := Fintype.ofFinite K
  obtain ⟨n, _, hcard⟩ := FiniteField.card K p
  apply IsPGroup.of_card (n := (n : ℕ) * Nat.card {β : ι // b.IsPos β})
  rw [positiveWitnessedWeightCompanionSubgroup_card P b O hc hm K hdiamond,
    Nat.card_eq_fintype_card, hcard, pow_mul]

theorem positiveWitnessedWeightCompanionSubgroup_isNilpotent :
    Group.IsNilpotent (positiveWitnessedWeightCompanionSubgroup P b O hc hm K) := by
  letI := Fintype.ofFinite K
  letI := positiveWitnessedWeightCompanionSubgroup_finite P b O hc hm K hdiamond
  obtain ⟨p, hp, _, hprime, _⟩ := FiniteField.card' K
  letI : CharP K p := hp
  letI : Fact p.Prime := ⟨hprime⟩
  exact (positiveWitnessedWeightCompanionSubgroup_isPGroup
    P b O hc hm K hdiamond p).isNilpotent

theorem positiveWitnessedWeightCompanionSubgroup_isSolvable :
    Group.IsSolvable (positiveWitnessedWeightCompanionSubgroup P b O hc hm K) := by
  letI := positiveWitnessedWeightCompanionSubgroup_isNilpotent P b O hc hm K hdiamond
  infer_instance

end Atlas.Chevalley
