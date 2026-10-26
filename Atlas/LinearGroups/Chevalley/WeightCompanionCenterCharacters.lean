import Atlas.LinearGroups.Chevalley.WeightCompanionCenterQuotient
import Atlas.LinearGroups.Chevalley.WeightCompanionCentralTorusConverse

/-! The whole center of the actual finite-field companion, with the genuine
weight-span premise, is the character group of the weight/root quotient. -/
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
  (K : Type*) [Field K] [Finite K] [Fintype κ]

/-- Full-center character description on the existing group, not a target
central extension specified by its order. -/
def weightCompanionCenterCharacterEquiv
    (hdiamond : SimpleDiamondProducts P b)
    (hspan : Submodule.span ℤ
      (Set.range (rootWeight P) ∪ {μ | ∃ a, μ ∈ O a}) = ⊤) :
    Subgroup.center (WeightCompanion P b O hc hm K) ≃*
      (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Kˣ) :=
  (MulEquiv.subgroupCongr
    (show Subgroup.center (WeightCompanion P b O hc hm K) =
        weightCompanionTorusSubgroup P b O hc hm K ⊓
          Subgroup.center (WeightCompanion P b O hc hm K) from
      (inf_eq_right.mpr
        (weightCompanion_center_le_torus_finiteField P b O hc hm K hdiamond)).symm)).trans
    (weightCompanionTorusCenterCharacterEquiv P b O hc hm K hspan)

theorem weightCompanion_center_card_eq_character
    (hdiamond : SimpleDiamondProducts P b)
    (hspan : Submodule.span ℤ
      (Set.range (rootWeight P) ∪ {μ | ∃ a, μ ∈ O a}) = ⊤) :
    Nat.card (Subgroup.center (WeightCompanion P b O hc hm K)) =
      Nat.card (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Kˣ) :=
  Nat.card_congr (weightCompanionCenterCharacterEquiv P b O hc hm K hdiamond hspan).toEquiv

/-- Transfer of the existing torus-parameter-kernel count to the full center. -/
theorem weightCompanion_center_card_eq_adjointTorusKernel
    (hdiamond : SimpleDiamondProducts P b)
    (hspan : Submodule.span ℤ
      (Set.range (rootWeight P) ∪ {μ | ∃ a, μ ∈ O a}) = ⊤) :
    Nat.card (Subgroup.center (WeightCompanion P b O hc hm K)) =
      Nat.card (adjointTorusParameters P b K).ker :=
  (weightCompanion_center_card_eq_character P b O hc hm K hdiamond hspan).trans
    (adjointTorusKernel_card P K b).symm

/-- A structural cardinal identity, with no formula for the adjoint group
assumed or inferred from a known family name. -/
theorem weightCompanion_card_eq_adjoint_mul_characters
    (hdiamond : SimpleDiamondProducts P b)
    (hspan : Submodule.span ℤ
      (Set.range (rootWeight P) ∪ {μ | ∃ a, μ ∈ O a}) = ⊤) :
    Nat.card (WeightCompanion P b O hc hm K) =
      Nat.card (Adjoint P b K) *
        Nat.card (Multiplicative (WeightLattice P ⧸ rootLattice P) →* Kˣ) := by
  rw [weightCompanion_card_eq_adjoint_mul_center P b O hc hm K hdiamond,
    weightCompanion_center_card_eq_character P b O hc hm K hdiamond hspan]

end Atlas.Chevalley
