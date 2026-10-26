import Atlas.LinearGroups.Chevalley.B2MarkedShortRoot
import Atlas.LinearGroups.Chevalley.Integral.MinusculeB2MarkedShortRoot
import Atlas.LinearGroups.Chevalley.WeightCompanionTorus

/-! Signed short-middle B2 normalization in the literal full companion group. -/
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
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

/-- For i short and j long, n_i sends n_j X_i(t)n_j⁻¹ to the same actual
root family with parameter -t, over every commutative coefficient ring. -/
theorem weightCompanionWeyl_b2_negates_short_conjugate_X
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (t : R) :
    weightCompanionWeyl P b O hc hm R i 1 *
        (weightCompanionWeyl P b O hc hm R j 1 * weightCompanionX P b O hc hm R i t *
          (weightCompanionWeyl P b O hc hm R j 1)⁻¹) *
        (weightCompanionWeyl P b O hc hm R i 1)⁻¹ =
      weightCompanionWeyl P b O hc hm R j 1 * weightCompanionX P b O hc hm R i (-t) *
        (weightCompanionWeyl P b O hc hm R j 1)⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointWeyl_b2_negates_short_conjugate_X P b hdiamond R i j hne hij hji t
  · funext a
    exact weightOrbit_b2_weyl_negates_short_conjugate_rootElements
      P (O a) (hc a) (hm a) R i.val j.val hij hji t

end Atlas.Chevalley
