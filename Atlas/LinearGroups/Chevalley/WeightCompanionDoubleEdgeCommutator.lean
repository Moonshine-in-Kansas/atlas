import Atlas.LinearGroups.Chevalley.AdjointOpposition
import Atlas.LinearGroups.Chevalley.B2WeylCommutator
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDoubleEdgeWord

/-! The mixed double-edge word in the actual simultaneous subgroup.
The adjoint block and every selected weight block are checked independently.
No injective projection, complete scalar kernel or whole-companion opposition
is assumed. -/

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

/-- Actual adjoint opposition transports only the adjoint block. -/
theorem adjointY_b2_commutator_eq_negative_weyl_product
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (s t : R) :
    let V (k : b.support) := adjointY P b R k 1 *
      adjointX P b R k (-1) * adjointY P b R k 1
    ⁅adjointY P b R i s, adjointY P b R j t⁆ =
      (V j * adjointY P b R i (-s * t) * (V j)⁻¹) *
      (V i * adjointY P b R j (s ^ 2 * t) * (V i)⁻¹) := by
  have h := congrArg (adjointOppositionEquiv P b R)
    (adjointX_b2_commutator_eq_weyl_product P b hdiamond R i j hne hij hji s t)
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

/-- Equality in the actual subgroup follows from its actual product blocks. -/
theorem weightCompanionX_b2_commutator_eq_weyl_product
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (s t : R) :
    ⁅weightCompanionX P b O hc hm R i s, weightCompanionX P b O hc hm R j t⁆ =
      (weightCompanionWeyl P b O hc hm R j 1 *
          weightCompanionX P b O hc hm R i (-s * t) *
          (weightCompanionWeyl P b O hc hm R j 1)⁻¹) *
      (weightCompanionWeyl P b O hc hm R i 1 *
          weightCompanionX P b O hc hm R j (s ^ 2 * t) *
          (weightCompanionWeyl P b O hc hm R i 1)⁻¹) := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointX_b2_commutator_eq_weyl_product P b hdiamond R i j hne hij hji s t
  · funext a
    exact weightOrbit_doubleEdge_rootElements_commutator P (O a) (hc a) (hm a) R
      i.val j.val hij hji s t

/-- The negative word uses the separately derived negative identity on each
original weight block. It does not lift the adjoint opposition to the companion. -/
theorem weightCompanionY_b2_commutator_eq_negative_weyl_product
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (s t : R) :
    let V (k : b.support) := weightCompanionY P b O hc hm R k 1 *
      weightCompanionX P b O hc hm R k (-1) * weightCompanionY P b O hc hm R k 1
    ⁅weightCompanionY P b O hc hm R i s, weightCompanionY P b O hc hm R j t⁆ =
      (V j * weightCompanionY P b O hc hm R i (-s * t) * (V j)⁻¹) *
      (V i * weightCompanionY P b O hc hm R j (s ^ 2 * t) * (V i)⁻¹) := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointY_b2_commutator_eq_negative_weyl_product
      P b hdiamond R i j hne hij hji s t
  · funext a
    exact weightOrbit_doubleEdge_lowering_rootElements_commutator P (O a) (hc a) (hm a) R
      i.val j.val hij hji s t

end Atlas.Chevalley
