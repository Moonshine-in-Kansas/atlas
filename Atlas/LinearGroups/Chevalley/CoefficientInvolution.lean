import Atlas.LinearGroups.Chevalley.WeightCompanionEquiv
import Atlas.FieldTheory.FiniteQuadraticExtension

/-! Frobenius involutions on the actual adjoint and minuscule-companion
groups over a quadratic finite-field extension. No twisted-group order or
simplicity assertion is built into these maps. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)
  (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def adjointFrobenius : Adjoint P b K ≃* Adjoint P b K :=
  adjointEquiv P b (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv

theorem adjointFrobenius_involutive (hdeg : Module.finrank F K = 2) :
    Function.Involutive (adjointFrobenius P b F K) := by
  intro g
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact Atlas.FiniteQuadratic.conjugation_involutive hdeg (g.val.val i j)

theorem adjointFrobenius_X (i : b.support) (t : K) :
    adjointFrobenius P b F K (adjointX P b K i t) =
      adjointX P b K i (t ^ Nat.card F) := by
  rw [adjointFrobenius, adjointEquiv_x]
  rw [show (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv t =
    t ^ Nat.card F from Atlas.FiniteQuadratic.conjugation_apply F K t]

theorem adjointFrobenius_Y (i : b.support) (t : K) :
    adjointFrobenius P b F K (adjointY P b K i t) =
      adjointY P b K i (t ^ Nat.card F) := by
  rw [adjointFrobenius, adjointEquiv_y]
  rw [show (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv t =
    t ^ Nat.card F from Atlas.FiniteQuadratic.conjugation_apply F K t]

variable (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)

def weightCompanionFrobenius :
    WeightCompanion P b O hclosed hmin K ≃* WeightCompanion P b O hclosed hmin K :=
  weightCompanionEquiv P b O hclosed hmin (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv

theorem weightCompanionFrobenius_involutive (hdeg : Module.finrank F K = 2) :
    Function.Involutive (weightCompanionFrobenius P b F K O hclosed hmin) := by
  classical
  intro g
  apply Subtype.ext
  apply Prod.ext
  · exact adjointFrobenius_involutive P b F K hdeg g.val.1
  · funext a
    apply Units.ext
    ext μ ν
    exact Atlas.FiniteQuadratic.conjugation_involutive hdeg ((g.val.2 a).val μ ν)

theorem weightCompanionFrobenius_X (i : b.support) (t : K) :
    weightCompanionFrobenius P b F K O hclosed hmin (weightCompanionX P b O hclosed hmin K i t) =
      weightCompanionX P b O hclosed hmin K i (t ^ Nat.card F) := by
  rw [weightCompanionFrobenius, weightCompanionEquiv_X]
  rw [show (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv t =
    t ^ Nat.card F from Atlas.FiniteQuadratic.conjugation_apply F K t]

theorem weightCompanionFrobenius_Y (i : b.support) (t : K) :
    weightCompanionFrobenius P b F K O hclosed hmin (weightCompanionY P b O hclosed hmin K i t) =
      weightCompanionY P b O hclosed hmin K i (t ^ Nat.card F) := by
  rw [weightCompanionFrobenius, weightCompanionEquiv_Y]
  rw [show (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv t =
    t ^ Nat.card F from Atlas.FiniteQuadratic.conjugation_apply F K t]

theorem weightCompanionFrobenius_rho (g : WeightCompanion P b O hclosed hmin K) :
    weightCompanionRho P b O hclosed hmin K (weightCompanionFrobenius P b F K O hclosed hmin g) =
      adjointFrobenius P b F K (weightCompanionRho P b O hclosed hmin K g) := rfl

end Atlas.Chevalley
