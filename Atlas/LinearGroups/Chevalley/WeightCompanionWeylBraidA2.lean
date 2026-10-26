import Atlas.LinearGroups.Chevalley.AdjointWeylBraidA2
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylBraidA2
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus

/-! Source candidate: actual A2 braid in the full simultaneous companion.
Each coordinate block is proved independently, without using rho injectivity. -/

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

theorem weightCompanionWeyl_a2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    weightCompanionWeyl P b O hc hm R i 1 *
        weightCompanionWeyl P b O hc hm R j 1 *
        weightCompanionWeyl P b O hc hm R i 1 =
      weightCompanionWeyl P b O hc hm R j 1 *
        weightCompanionWeyl P b O hc hm R i 1 *
        weightCompanionWeyl P b O hc hm R j 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointWeyl_a2_braid P b R i j hij hji
  · funext a
    exact weightOrbit_weylMatrixUnit_a2_braid P (O a) (hc a) (hm a) R
      i.val j.val hij hji

end Atlas.Chevalley
