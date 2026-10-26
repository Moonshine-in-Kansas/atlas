import Atlas.LinearGroups.Chevalley.WeightCompanion

/-! An empty extra weight family gives exactly the actual adjoint group. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι] [IsEmpty κ]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- With no extra blocks, the literal adjoint projection loses no information. -/
theorem weightCompanionRho_injective_of_isEmpty :
    Function.Injective (weightCompanionRho P b O hclosed hmin R) := by
  intro g h he
  apply Subtype.ext
  apply Prod.ext
  · exact he
  · funext a
    exact isEmptyElim a

/-- Explicit equivalence of the actual generated groups, not recognition by order. -/
def weightCompanionAdjointEquivOfIsEmpty :
    WeightCompanion P b O hclosed hmin R ≃* Adjoint P b R :=
  MulEquiv.ofBijective (weightCompanionRho P b O hclosed hmin R)
    ⟨weightCompanionRho_injective_of_isEmpty P b O hclosed hmin R,
      weightCompanionRho_surjective P b O hclosed hmin R⟩

@[simp] theorem weightCompanionAdjointEquivOfIsEmpty_apply
    (g : WeightCompanion P b O hclosed hmin R) :
    weightCompanionAdjointEquivOfIsEmpty P b O hclosed hmin R g =
      weightCompanionRho P b O hclosed hmin R g := rfl

@[simp] theorem weightCompanionAdjointEquivOfIsEmpty_X (i : b.support) (t : R) :
    weightCompanionAdjointEquivOfIsEmpty P b O hclosed hmin R
      (weightCompanionX P b O hclosed hmin R i t) = adjointX P b R i t := rfl

@[simp] theorem weightCompanionAdjointEquivOfIsEmpty_Y (i : b.support) (t : R) :
    weightCompanionAdjointEquivOfIsEmpty P b O hclosed hmin R
      (weightCompanionY P b O hclosed hmin R i t) = adjointY P b R i t := rfl

end Atlas.Chevalley
