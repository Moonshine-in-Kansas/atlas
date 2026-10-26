import Atlas.LinearGroups.Chevalley.WeightCompanionNonAdjacentWeyl

/-! Actual Weyl words fix both simple-root families at a zero Cartan edge.
The unit parameter of the Weyl word is arbitrary. This is a literal full-group
identity, not an assertion about arbitrary orthogonal nonsimple roots. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

theorem weightCompanionWeyl_commute_X_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0)
    (a : Rˣ) (t : R) :
    Commute (weightCompanionWeyl P b O hc hm R i a)
      (weightCompanionX P b O hc hm R j t) := by
  have hx := weightCompanionX_commute_of_zero_cartan
    P b hdiamond O hc hm R i j hne hji a.val t
  have hy := (weightCompanionX_commute_Y
    P b hdiamond O hc hm R j i hne.symm t (-a.inv)).symm
  unfold weightCompanionWeyl
  exact (hx.mul_left hy).mul_left hx

theorem weightCompanionWeyl_commute_Y_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0)
    (a : Rˣ) (t : R) :
    Commute (weightCompanionWeyl P b O hc hm R i a)
      (weightCompanionY P b O hc hm R j t) := by
  have hx := weightCompanionX_commute_Y
    P b hdiamond O hc hm R i j hne a.val t
  have hy := weightCompanionY_commute_of_zero_cartan
    P b hdiamond O hc hm R i j hne hji (-a.inv) t
  unfold weightCompanionWeyl
  exact (hx.mul_left hy).mul_left hx

/-- A zero-edge Weyl word fixes the entire actual positive simple-root family. -/
theorem weightCompanionWeyl_conjugate_X_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0)
    (a : Rˣ) (t : R) :
    weightCompanionWeyl P b O hc hm R i a * weightCompanionX P b O hc hm R j t *
      (weightCompanionWeyl P b O hc hm R i a)⁻¹ = weightCompanionX P b O hc hm R j t := by
  rw [(weightCompanionWeyl_commute_X_of_zero_cartan P b hdiamond O hc hm R i j hne hji a t).eq,
    mul_assoc, mul_inv_cancel, mul_one]

/-- The same zero-edge Weyl word fixes the actual negative simple-root family. -/
theorem weightCompanionWeyl_conjugate_Y_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0)
    (a : Rˣ) (t : R) :
    weightCompanionWeyl P b O hc hm R i a * weightCompanionY P b O hc hm R j t *
      (weightCompanionWeyl P b O hc hm R i a)⁻¹ = weightCompanionY P b O hc hm R j t := by
  rw [(weightCompanionWeyl_commute_Y_of_zero_cartan P b hdiamond O hc hm R i j hne hji a t).eq,
    mul_assoc, mul_inv_cancel, mul_one]

theorem weightCompanionRho_conjugate_X_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0)
    (a : Rˣ) (t : R) :
    weightCompanionRho P b O hc hm R
      (weightCompanionWeyl P b O hc hm R i a * weightCompanionX P b O hc hm R j t *
        (weightCompanionWeyl P b O hc hm R i a)⁻¹) = adjointX P b R j t := by
  rw [weightCompanionWeyl_conjugate_X_of_zero_cartan P b hdiamond O hc hm R i j hne hji a t,
    weightCompanionRho_X]

theorem weightCompanionRho_conjugate_Y_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0)
    (a : Rˣ) (t : R) :
    weightCompanionRho P b O hc hm R
      (weightCompanionWeyl P b O hc hm R i a * weightCompanionY P b O hc hm R j t *
        (weightCompanionWeyl P b O hc hm R i a)⁻¹) = adjointY P b R j t := by
  rw [weightCompanionWeyl_conjugate_Y_of_zero_cartan P b hdiamond O hc hm R i j hne hji a t,
    weightCompanionRho_Y]

end Atlas.Chevalley
