import Atlas.LinearGroups.Chevalley.WeightCompanionFiniteCenter
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card

/-! The actual quotient by the full center is the actual adjoint model.
Only the already constructed projection and its precise kernel are used.
No simplicity, weight-span condition or recognized group is assumed. -/
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

/-- First isomorphism theorem for the existing literal projection, with
its proved full center substituted for the kernel. -/
def weightCompanionCenterQuotientAdjointEquiv
    (hdiamond : SimpleDiamondProducts P b) :
    WeightCompanion P b O hc hm K ⧸
        Subgroup.center (WeightCompanion P b O hc hm K) ≃* Adjoint P b K :=
  (QuotientGroup.quotientMulEquivOfEq
    (weightCompanion_center_eq_rhoKernel_finiteField P b O hc hm K hdiamond)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (weightCompanionRho P b O hc hm K)
        (weightCompanionRho_surjective P b O hc hm K))

/-- The quotient equivalence is induced by the original adjoint block map. -/
theorem weightCompanionCenterQuotientAdjointEquiv_mk
    (hdiamond : SimpleDiamondProducts P b) (g : WeightCompanion P b O hc hm K) :
    weightCompanionCenterQuotientAdjointEquiv P b O hc hm K hdiamond
      (QuotientGroup.mk g) = weightCompanionRho P b O hc hm K g := rfl

/-- Lagrange's cardinal identity for the actual central quotient. This is not
an explicit formula for the order of either whole group. -/
theorem weightCompanion_card_eq_adjoint_mul_center
    (hdiamond : SimpleDiamondProducts P b) :
    Nat.card (WeightCompanion P b O hc hm K) =
      Nat.card (Adjoint P b K) *
        Nat.card (Subgroup.center (WeightCompanion P b O hc hm K)) := by
  calc
    Nat.card (WeightCompanion P b O hc hm K) =
        Nat.card (WeightCompanion P b O hc hm K ⧸
          Subgroup.center (WeightCompanion P b O hc hm K)) *
          Nat.card (Subgroup.center (WeightCompanion P b O hc hm K)) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = _ := congrArg
      (fun n => n * Nat.card (Subgroup.center (WeightCompanion P b O hc hm K)))
      (Nat.card_congr
        (weightCompanionCenterQuotientAdjointEquiv P b O hc hm K hdiamond).toEquiv)

end Atlas.Chevalley
