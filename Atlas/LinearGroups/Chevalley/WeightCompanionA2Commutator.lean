import Atlas.LinearGroups.Chevalley.AdjointOpposition
import Atlas.LinearGroups.Chevalley.A2WeylCommutator
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus
import Atlas.LinearGroups.Chevalley.Integral.MinusculeA2WeylPinning

/-! Pinned A2 commutators in the actual simultaneous adjoint/minuscule subgroup.
Every actual block is checked. No injectivity or central-kernel assertion about
the projection to the adjoint group is assumed. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule
open scoped commutatorElement

section AdjointNegative
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R]

include hdiamond

/-- Opposition is used only on the actual adjoint block, where its normalizing
action has been proved. The negative Weyl word is Y_i(1) X_i(-1) Y_i(1). -/
theorem adjointY_a2_commutator_eq_negative_weyl_conjugate
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (s t : R) :
    let V := adjointY P b R i 1 * adjointX P b R i (-1) * adjointY P b R i 1
    ⁅adjointY P b R i s, adjointY P b R j t⁆ =
      V * adjointY P b R j (s * t) * V⁻¹ := by
  have h := congrArg (adjointOppositionEquiv P b R)
    (adjointX_a2_commutator_eq_weyl_conjugate P b hdiamond R i j hne hij hji s t)
  simpa only [map_commutatorElement, map_mul, map_inv, adjointWeyl,
    adjointOppositionEquiv_X, adjointOppositionEquiv_Y,
    Units.inv_eq_val_inv, inv_one, Units.val_one] using h
end AdjointNegative

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

/-- Equality in the actual generated subgroup, proved on the adjoint block and
each actual minuscule weight block independently. -/
theorem weightCompanionX_a2_commutator_eq_weyl_conjugate
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (s t : R) :
    ⁅weightCompanionX P b O hc hm R i s, weightCompanionX P b O hc hm R j t⁆ =
      weightCompanionWeyl P b O hc hm R i 1 *
        weightCompanionX P b O hc hm R j (s * t) *
          (weightCompanionWeyl P b O hc hm R i 1)⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointX_a2_commutator_eq_weyl_conjugate P b hdiamond R i j hne hij hji s t
  · funext a
    exact weightOrbit_a2_rootElements_commutator P (O a) (hc a) (hm a) R
      i.val j.val hij hji s t

/-- The negative identity uses the separately proved lowering relation on each
weight block. No whole-companion opposition or negation-closed orbit is assumed. -/
theorem weightCompanionY_a2_commutator_eq_negative_weyl_conjugate
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (s t : R) :
    let V := weightCompanionY P b O hc hm R i 1 *
      weightCompanionX P b O hc hm R i (-1) * weightCompanionY P b O hc hm R i 1
    ⁅weightCompanionY P b O hc hm R i s, weightCompanionY P b O hc hm R j t⁆ =
      V * weightCompanionY P b O hc hm R j (s * t) * V⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointY_a2_commutator_eq_negative_weyl_conjugate
      P b hdiamond R i j hne hij hji s t
  · funext a
    exact weightOrbit_a2_lowering_rootElements_commutator P (O a) (hc a) (hm a) R
      i.val j.val hij hji s t

end Atlas.Chevalley
