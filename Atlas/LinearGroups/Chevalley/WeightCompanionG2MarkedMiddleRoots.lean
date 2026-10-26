import Atlas.LinearGroups.Chevalley.G2MarkedMiddleRoots
import Atlas.LinearGroups.Chevalley.Integral.MinusculeTripleEdgeTrivial
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus

/-! Two marked G2 middle-family identities in the actual complete companion.
The adjoint integer-operator transfer and actual trivial minuscule restrictions
are assembled separately. No projection injectivity is used. -/

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

theorem weightCompanionWeyl_g2_fixes_short_middle_X
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (t : R) :
    weightCompanionWeyl P b O hc hm R j 1 *
      ((weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1) *
        weightCompanionX P b O hc hm R i t *
        (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1)⁻¹) *
      (weightCompanionWeyl P b O hc hm R j 1)⁻¹ =
      (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1) *
        weightCompanionX P b O hc hm R i t *
        (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionWeyl P b O hc hm R j 1)⁻¹ := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · exact adjointWeyl_g2_fixes_short_middle_X P b hdiamond R i j hne hij hji t
  · funext a
    let T := stringsOfWeightOrbit P (O a) (hc a) (hm a)
    let wi := T.weylMatrixUnit R i.val 1
    let wj := T.weylMatrixUnit R j.val 1
    let x := weightOrbitRootElement P (O a) (hc a) (hm a) R i.val (-1) (by decide) t
    change wj * ((wi * wj) * x * (wi * wj)⁻¹) * wj⁻¹ =
      (wi * wj) * x * (wi * wj)⁻¹
    have hi : wi = 1 := weightOrbit_tripleEdge_weylMatrixUnit_eq_one
      P (O a) (hc a) (hm a) R i.val j.val i.val hij hji (Or.inl rfl) 1
    have hj : wj = 1 := weightOrbit_tripleEdge_weylMatrixUnit_eq_one
      P (O a) (hc a) (hm a) R i.val j.val j.val hij hji (Or.inr rfl) 1
    simp only [hi, hj, one_mul, inv_one, mul_one]

theorem weightCompanionWeyl_g2_fixes_long_middle_X
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (t : R) :
    weightCompanionWeyl P b O hc hm R i 1 *
      ((weightCompanionWeyl P b O hc hm R j 1 * weightCompanionWeyl P b O hc hm R i 1) *
        weightCompanionX P b O hc hm R j t *
        (weightCompanionWeyl P b O hc hm R j 1 * weightCompanionWeyl P b O hc hm R i 1)⁻¹) *
      (weightCompanionWeyl P b O hc hm R i 1)⁻¹ =
      (weightCompanionWeyl P b O hc hm R j 1 * weightCompanionWeyl P b O hc hm R i 1) *
        weightCompanionX P b O hc hm R j t *
        (weightCompanionWeyl P b O hc hm R j 1 * weightCompanionWeyl P b O hc hm R i 1)⁻¹ := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · exact adjointWeyl_g2_fixes_long_middle_X P b hdiamond R i j hne hij hji t
  · funext a
    let T := stringsOfWeightOrbit P (O a) (hc a) (hm a)
    let wi := T.weylMatrixUnit R i.val 1
    let wj := T.weylMatrixUnit R j.val 1
    let x := weightOrbitRootElement P (O a) (hc a) (hm a) R j.val (-1) (by decide) t
    change wi * ((wj * wi) * x * (wj * wi)⁻¹) * wi⁻¹ =
      (wj * wi) * x * (wj * wi)⁻¹
    have hi : wi = 1 := weightOrbit_tripleEdge_weylMatrixUnit_eq_one
      P (O a) (hc a) (hm a) R i.val j.val i.val hij hji (Or.inl rfl) 1
    have hj : wj = 1 := weightOrbit_tripleEdge_weylMatrixUnit_eq_one
      P (O a) (hc a) (hm a) R i.val j.val j.val hij hji (Or.inr rfl) 1
    simp only [hi, hj, one_mul, inv_one, mul_one]

end Atlas.Chevalley
