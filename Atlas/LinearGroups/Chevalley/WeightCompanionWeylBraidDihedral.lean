import Atlas.LinearGroups.Chevalley.AdjointWeylBraidDihedral
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylBraidDihedral
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus

/-! Actual length-four and length-six braid identities in the full simultaneous
companion. The adjoint and every selected weight block are checked separately. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

theorem weightCompanionWeyl_b2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    weightCompanionWeyl P b O hc hm R i 1 *
      weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionWeyl P b O hc hm R i 1 *
      weightCompanionWeyl P b O hc hm R j 1 =
      weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionWeyl P b O hc hm R i 1 *
      weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionWeyl P b O hc hm R i 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointWeyl_b2_braid P b R i j hij hji
  · funext a
    exact weightOrbit_weylMatrixUnit_b2_braid P (O a) (hc a) (hm a) R
      i.val j.val hij hji

theorem weightCompanionWeyl_g2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    weightCompanionWeyl P b O hc hm R i 1 *
      weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionWeyl P b O hc hm R i 1 *
      weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionWeyl P b O hc hm R i 1 *
      weightCompanionWeyl P b O hc hm R j 1 =
      weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionWeyl P b O hc hm R i 1 *
      weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionWeyl P b O hc hm R i 1 *
      weightCompanionWeyl P b O hc hm R j 1 *
      weightCompanionWeyl P b O hc hm R i 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointWeyl_g2_braid P b R i j hij hji
  · funext a
    exact weightOrbit_weylMatrixUnit_g2_braid P (O a) (hc a) (hm a) R
      i.val j.val hij hji

end Atlas.Chevalley
