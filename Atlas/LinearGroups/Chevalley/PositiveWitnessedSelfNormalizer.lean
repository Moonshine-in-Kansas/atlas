import Atlas.GroupTheory.DoubleCosetNormalizerCard
import Atlas.LinearGroups.Chevalley.PositiveWitnessedCellCoordinates
import Atlas.LinearGroups.Chevalley.PositiveWitnessedWeylCellDecomposition
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-! Over a finite field the actual positive/torus subgroup is self-normalizing.
Only individual cell cardinalities are used, never a full-group order formula. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K] [Finite K] [Fintype κ]

theorem positiveWitnessedTorusJoin_mem_of_mem_normalizer
    (hdiamond : SimpleDiamondProducts P b)
    (g : WeightCompanion P b O hc hm K)
    (hg : g ∈ Subgroup.normalizer (positiveWitnessedTorusJoin P b O hc hm K)) :
    g ∈ positiveWitnessedTorusJoin P b O hc hm K := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  obtain ⟨w, hw⟩ := exists_mem_positiveWitnessedWeylCell P b O hc hm K hdiamond g
  change g ∈ DoubleCoset.doubleCoset
    (weightCompanionTitsLift P b O hc hm K w).val B B at hw
  have hsets := DoubleCoset.doubleCoset_eq_of_mem hw
  have hc : Nat.card K ^ rootWeylLength P b w⁻¹ * Nat.card B = Nat.card B := by
    calc
      _ = Nat.card ↥(DoubleCoset.doubleCoset
          (weightCompanionTitsLift P b O hc hm K w).val B B) :=
        (positiveWitnessed_doubleCell_card P b O hc hm K hdiamond w).symm
      _ = Nat.card ↥(DoubleCoset.doubleCoset g B B) :=
        congrArg (fun S : Set (WeightCompanion P b O hc hm K) => Nat.card S) hsets.symm
      _ = Nat.card B := doubleCoset_card_of_mem_normalizer B g hg
  have hp : Nat.card K ^ rootWeylLength P b w⁻¹ = 1 :=
    Nat.mul_right_cancel (show 0 < Nat.card B from Nat.card_pos)
      (hc.trans (one_mul (Nat.card B)).symm)
  have hq : 1 < Nat.card K := by
    letI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hl : rootWeylLength P b w⁻¹ = 0 := by
    by_contra hne
    exact (one_lt_pow₀ hq hne).ne' hp
  have hw1 : w = 1 := inv_eq_one.mp ((rootWeylLength_eq_zero_iff P b w⁻¹).mp hl)
  rw [hw1, weightCompanionTitsLift_one] at hw
  obtain ⟨a, ha, c, hcb, he⟩ := DoubleCoset.mem_doubleCoset.mp hw
  rw [he]
  change a * 1 * c ∈ B
  simpa only [mul_one] using B.mul_mem ha hcb

theorem positiveWitnessedTorusJoin_normalizer_eq
    (hdiamond : SimpleDiamondProducts P b) :
    Subgroup.normalizer (positiveWitnessedTorusJoin P b O hc hm K) =
      positiveWitnessedTorusJoin P b O hc hm K := by
  apply le_antisymm
  · intro g hg
    exact positiveWitnessedTorusJoin_mem_of_mem_normalizer P b O hc hm K hdiamond g hg
  · exact Subgroup.le_normalizer

theorem weightCompanion_center_le_positiveWitnessedTorusJoin
    (hdiamond : SimpleDiamondProducts P b) :
    Subgroup.center (WeightCompanion P b O hc hm K) ≤
      positiveWitnessedTorusJoin P b O hc hm K := by
  rw [← positiveWitnessedTorusJoin_normalizer_eq P b O hc hm K hdiamond]
  exact Subgroup.center_le_normalizer _

end Atlas.Chevalley
