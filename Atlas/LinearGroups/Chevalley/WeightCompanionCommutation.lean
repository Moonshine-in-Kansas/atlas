import Atlas.LinearGroups.Chevalley.WeightCompanion
import Atlas.LinearGroups.Chevalley.Integral.LocalDiamondCommutation
import Atlas.LinearGroups.Chevalley.Integral.MinusculeOpposite

/-! Simultaneous opposite-simple commutation on every actual weight block. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : Integral.SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

theorem weightCompanionRootX_commute_rootY (i j : b.support) (hij : i ≠ j) (s t : R) :
    Commute (weightCompanionRootX P b O hc hm R i s)
      (weightCompanionRootY P b O hc hm R j t) := by
  change _ * _ = _ * _
  apply Prod.ext
  · exact (adjointX_commute_adjointY_of_diamond P b hdiamond R i j hij s t).eq
  · funext a
    exact (weightOrbit_opposite_rootElements_commute P (O a) (hc a) (hm a) b i j hij R s t).eq

theorem weightCompanionX_commute_Y (i j : b.support) (hij : i ≠ j) (s t : R) :
    Commute (weightCompanionX P b O hc hm R i s)
      (weightCompanionY P b O hc hm R j t) := by
  change _ * _ = _ * _
  apply Subtype.ext
  exact (weightCompanionRootX_commute_rootY P b hdiamond O hc hm R i j hij s t).eq

end Atlas.Chevalley
