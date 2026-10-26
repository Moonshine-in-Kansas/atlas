import Atlas.LinearGroups.Chevalley.WeightCompanionA2Commutator
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSquare
import Atlas.LinearGroups.Chevalley.WeightCompanionCrossTorus
import Mathlib.Tactic.Group

/-! Actual simple-to-simple transport across a single A2 edge. The full
companion identity is obtained from the already checked A2 commutator and
rank-one torus identities. No projection kernel or root-choice coherence is
assumed. The sign is positive in the existing Weyl-word convention. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule
open scoped commutatorElement

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

/-- Swapping the two A2 origins negates the additive root parameter. This is
an equality in the actual companion, not just on its adjoint image. -/
theorem weightCompanionWeyl_a2_X_swap_conjugate
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    weightCompanionWeyl P b O hc hm R j 1 * weightCompanionX P b O hc hm R i t *
        (weightCompanionWeyl P b O hc hm R j 1)⁻¹ =
      weightCompanionWeyl P b O hc hm R i 1 * weightCompanionX P b O hc hm R j (-t) *
        (weightCompanionWeyl P b O hc hm R i 1)⁻¹ := by
  have hforward := weightCompanionX_a2_commutator_eq_weyl_conjugate
    P b hdiamond O hc hm R i j hne hij hji 1 t
  have hreverse := weightCompanionX_a2_commutator_eq_weyl_conjugate
    P b hdiamond O hc hm R j i hne.symm hji hij t 1
  simp only [one_mul] at hforward
  simp only [mul_one] at hreverse
  have hneg : weightCompanionX P b O hc hm R j (-t) =
      (weightCompanionX P b O hc hm R j t)⁻¹ :=
    map_inv (weightCompanionXHom P b O hc hm R j) (Multiplicative.ofAdd t)
  calc
    _ = ⁅weightCompanionX P b O hc hm R j t,
          weightCompanionX P b O hc hm R i 1⁆ := hreverse.symm
    _ = ⁅weightCompanionX P b O hc hm R i 1,
          weightCompanionX P b O hc hm R j t⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = (weightCompanionWeyl P b O hc hm R i 1 *
          weightCompanionX P b O hc hm R j t *
          (weightCompanionWeyl P b O hc hm R i 1)⁻¹)⁻¹ :=
      congrArg Inv.inv hforward
    _ = _ := by rw [hneg]; simp only [mul_inv_rev, inv_inv, mul_assoc]

/-- For an A2 edge, the literal product n_i n_j sends X_i(t) to X_j(t),
without changing its parameter or imposing a characteristic restriction. -/
theorem weightCompanionWeyl_a2_transport_X
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1) *
        weightCompanionX P b O hc hm R i t *
        (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1)⁻¹ =
      weightCompanionX P b O hc hm R j t := by
  let ni := weightCompanionWeyl P b O hc hm R i 1
  let nj := weightCompanionWeyl P b O hc hm R j 1
  have hswap := weightCompanionWeyl_a2_X_swap_conjugate
    P b hdiamond O hc hm R i j hne hij hji t
  change nj * weightCompanionX P b O hc hm R i t * nj⁻¹ =
    ni * weightCompanionX P b O hc hm R j (-t) * ni⁻¹ at hswap
  have hsquare : ni * ni = weightCompanionTorus P b O hc hm R i (-1) := by
    simpa only [pow_two] using weightCompanionWeyl_one_sq P b O hc hm R i
  have htorus : weightCompanionTorus P b O hc hm R i (-1) *
        weightCompanionX P b O hc hm R j (-t) *
        (weightCompanionTorus P b O hc hm R i (-1))⁻¹ =
      weightCompanionX P b O hc hm R j t := by
    simpa only [hji, zpow_neg_one, inv_neg, inv_one, Units.val_neg,
      Units.val_one, neg_one_mul, neg_neg] using
      weightCompanionTorus_conjugate_X_cross P b O hc hm R j i (-1) (-t)
  change (ni * nj) * weightCompanionX P b O hc hm R i t * (ni * nj)⁻¹ = _
  calc
    _ = ni * (nj * weightCompanionX P b O hc hm R i t * nj⁻¹) * ni⁻¹ := by group
    _ = ni * (ni * weightCompanionX P b O hc hm R j (-t) * ni⁻¹) * ni⁻¹ := by rw [hswap]
    _ = (ni * ni) * weightCompanionX P b O hc hm R j (-t) * (ni * ni)⁻¹ := by group
    _ = _ := by rw [hsquare]; exact htorus

/-- Applying the existing adjoint projection to the full transport identity.
Only functoriality is used, not injectivity of that projection. -/
theorem weightCompanionRho_a2_transport_X
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (t : R) :
    weightCompanionRho P b O hc hm R
      ((weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1) *
        weightCompanionX P b O hc hm R i t *
        (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1)⁻¹) =
      adjointX P b R j t := by
  rw [weightCompanionWeyl_a2_transport_X P b hdiamond O hc hm R i j hne hij hji t,
    weightCompanionRho_X]

end Atlas.Chevalley
