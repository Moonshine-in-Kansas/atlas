import Atlas.LinearGroups.Chevalley.G2WeylCommutator
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus
import Atlas.LinearGroups.Chevalley.Integral.MinusculeTripleEdgeTrivial

/-! The four-factor G2 commutator in the actual full companion model.
The adjoint block uses integral polynomial descent; each selected minuscule
block uses its already proved triple-edge triviality. No injectivity of the
adjoint projection is assumed. This source candidate is unchecked. -/

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
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

/-- The literal four-factor G2 identity holds in the simultaneous adjoint
and selected minuscule subgroup, uniformly over every commutative ring. -/
theorem weightCompanionX_g2_commutator_eq_weyl_product
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (s t : R) :
    ⁅weightCompanionX P b O hc hm R i s, weightCompanionX P b O hc hm R j t⁆ =
      (weightCompanionWeyl P b O hc hm R j 1 *
        weightCompanionX P b O hc hm R i (-s*t) *
        (weightCompanionWeyl P b O hc hm R j 1)⁻¹) *
      ((weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1) *
        weightCompanionX P b O hc hm R i (s^2*t) *
        (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1)⁻¹) *
      (weightCompanionWeyl P b O hc hm R i 1 *
        weightCompanionX P b O hc hm R j (s^3*t) *
        (weightCompanionWeyl P b O hc hm R i 1)⁻¹) *
      ((weightCompanionWeyl P b O hc hm R j 1 * weightCompanionWeyl P b O hc hm R i 1) *
        weightCompanionX P b O hc hm R j (2*s^3*t^2) *
        (weightCompanionWeyl P b O hc hm R j 1 * weightCompanionWeyl P b O hc hm R i 1)⁻¹) := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · exact adjointX_g2_commutator_eq_weyl_product P b hdiamond R i j hne hij hji s t
  · funext a
    let T := stringsOfWeightOrbit P (O a) (hc a) (hm a)
    let wi := T.weylMatrixUnit R i.val 1
    let wj := T.weylMatrixUnit R j.val 1
    let xi (u : R) := weightOrbitRootElement P (O a) (hc a) (hm a) R i.val (-1) (by decide) u
    let xj (u : R) := weightOrbitRootElement P (O a) (hc a) (hm a) R j.val (-1) (by decide) u
    change ⁅xi s, xj t⁆ =
      (wj * xi (-s*t) * wj⁻¹) *
      ((wi * wj) * xi (s^2*t) * (wi * wj)⁻¹) *
      (wi * xj (s^3*t) * wi⁻¹) *
      ((wj * wi) * xj (2*s^3*t^2) * (wj * wi)⁻¹)
    have hi : wi = 1 := weightOrbit_tripleEdge_weylMatrixUnit_eq_one
      P (O a) (hc a) (hm a) R i.val j.val i.val hij hji (Or.inl rfl) 1
    have hj : wj = 1 := weightOrbit_tripleEdge_weylMatrixUnit_eq_one
      P (O a) (hc a) (hm a) R i.val j.val j.val hij hji (Or.inr rfl) 1
    have hxi (u : R) : xi u = 1 := weightOrbit_tripleEdge_rootElement_eq_one
      P (O a) (hc a) (hm a) R i.val j.val i.val hij hji (Or.inl rfl) (-1) (by decide) u
    have hxj (u : R) : xj u = 1 := weightOrbit_tripleEdge_rootElement_eq_one
      P (O a) (hc a) (hm a) R i.val j.val j.val hij hji (Or.inr rfl) (-1) (by decide) u
    simp only [hi, hj, hxi, hxj, commutatorElement_def, inv_one, one_mul]

end Atlas.Chevalley
