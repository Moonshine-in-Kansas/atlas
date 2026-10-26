import Atlas.LinearGroups.Chevalley.PositiveWitnessedCellCoordinates
import Atlas.LinearGroups.Chevalley.PositiveWitnessedWeylCellDecomposition
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusOrder
import Atlas.LinearGroups.Chevalley.RootData.RootWeylPoincare

/-! The order of the actual companion as a Weyl-length sum. Evaluation of
that sum as a product of fundamental degrees is a separate obligation. -/
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
  (K : Type*) [Field K] [Finite K] [Fintype κ]
local instance : Fintype P.weylGroupToPerm.range := Fintype.ofFinite _

theorem weightCompanion_card_eq_borel_mul_weylSum
    (hdiamond : SimpleDiamondProducts P b) :
    Nat.card (WeightCompanion P b O hc hm K) =
      Nat.card (positiveWitnessedTorusJoin P b O hc hm K) *
        rootWeylPoincareEval P b (Nat.card K) := by
  calc
    _ = Nat.card (Σ w : P.weylGroupToPerm.range,
        positiveWitnessedWeylCell P b O hc hm K w) :=
      (Nat.card_congr (positiveWitnessedWeylCellSigmaEquiv P b O hc hm K hdiamond)).symm
    _ = ∑ w : P.weylGroupToPerm.range,
        Nat.card (positiveWitnessedWeylCell P b O hc hm K w) := Nat.card_sigma
    _ = ∑ w : P.weylGroupToPerm.range,
        Nat.card K ^ rootWeylLength P b w *
          Nat.card (positiveWitnessedTorusJoin P b O hc hm K) := by
      apply Finset.sum_congr rfl
      intro w hw
      simpa only [positiveWitnessedWeylCell, rootWeylLength_inv] using
        positiveWitnessed_doubleCell_card P b O hc hm K hdiamond w
    _ = _ := by rw [← Finset.sum_mul, mul_comm]; rfl

theorem weightCompanion_card_eq_root_torus_weylSum
    (hdiamond : SimpleDiamondProducts P b) :
    Nat.card (WeightCompanion P b O hc hm K) =
      Nat.card K ^ Nat.card {β : ι // b.IsPos β} *
        Nat.card (weightCompanionTorusSubgroup P b O hc hm K) *
        rootWeylPoincareEval P b (Nat.card K) := by
  rw [weightCompanion_card_eq_borel_mul_weylSum P b O hc hm K hdiamond,
    positiveWitnessedTorusJoin_card P b O hc hm K hdiamond]

theorem weightCompanion_card_eq_spanning_weylSum
    (hdiamond : SimpleDiamondProducts P b)
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪ {μ | ∃ k, μ ∈ O k}) = ⊤) :
    Nat.card (WeightCompanion P b O hc hm K) =
      Nat.card K ^ Nat.card {β : ι // b.IsPos β} *
        (Nat.card K - 1) ^ Nat.card b.support *
        rootWeylPoincareEval P b (Nat.card K) := by
  rw [weightCompanion_card_eq_root_torus_weylSum P b O hc hm K hdiamond,
    weightCompanionTorus_card P b O hc hm K hspan, Nat.card_units]

end Atlas.Chevalley
