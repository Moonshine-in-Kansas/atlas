import Atlas.LinearGroups.Chevalley.AdjointWeylSameRoot
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylSameRoot
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSquare
import Atlas.LinearGroups.Chevalley.WeightCompanionCommutation
import Mathlib.Tactic.Group

/-! Actual same-root Weyl exchange on every companion block, and its
consequence for a distinct simple-root conjugate. No adjoint faithfulness,
whole scalar kernel, or root-label-only inference is used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- The literal full companion Weyl word exchanges the negative root group
with the positive root group, with the actual parameter sign. -/
theorem weightCompanionWeyl_one_conjugate_Y_same (i : b.support) (t : R) :
    weightCompanionWeyl P b O hc hm R i 1 * weightCompanionY P b O hc hm R i t *
      (weightCompanionWeyl P b O hc hm R i 1)⁻¹ =
        weightCompanionX P b O hc hm R i (-t) := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointWeyl_one_conjugate_Y_same P b R i t
  · funext a
    exact (stringsOfWeightOrbit P (O a) (hc a) (hm a)).weylMatrixUnit_one_conjugate_lowering
      R i.val t

/-- The reverse exchange follows from the proved rank-one square and torus
scaling. It has no characteristic, nontriviality, or diamond premise. -/
theorem weightCompanionWeyl_one_conjugate_X_same (i : b.support) (t : R) :
    weightCompanionWeyl P b O hc hm R i 1 * weightCompanionX P b O hc hm R i t *
      (weightCompanionWeyl P b O hc hm R i 1)⁻¹ =
        weightCompanionY P b O hc hm R i (-t) := by
  let n := weightCompanionWeyl P b O hc hm R i 1
  have hswap : n * weightCompanionY P b O hc hm R i (-t) * n⁻¹ =
      weightCompanionX P b O hc hm R i t := by
    simpa only [n, neg_neg] using
      weightCompanionWeyl_one_conjugate_Y_same P b O hc hm R i (-t)
  change n * weightCompanionX P b O hc hm R i t * n⁻¹ = _
  calc
    n * weightCompanionX P b O hc hm R i t * n⁻¹ =
        n * (n * weightCompanionY P b O hc hm R i (-t) * n⁻¹) * n⁻¹ := by rw [hswap]
    _ = n ^ 2 * weightCompanionY P b O hc hm R i (-t) * (n ^ 2)⁻¹ := by
      simp only [pow_two]
      group
    _ = weightCompanionY P b O hc hm R i (-t) := by
      rw [show n ^ 2 = weightCompanionTorus P b O hc hm R i (-1) from
        weightCompanionWeyl_one_sq P b O hc hm R i]
      simpa only [Units.inv_eq_val_inv, Units.val_neg, Units.val_one,
        inv_neg, inv_one, neg_sq, one_pow, one_mul] using
        weightCompanionTorus_conjugate_Y P b O hc hm R i (-1) (-t)

/-- For distinct simple nodes, X_i commutes with the actual n_i-conjugate of
X_j. In B2 this is precisely commutation with the highest long-root family.
The only extra premise is the established cross-node diamond condition. -/
theorem weightCompanionX_commute_sameWeyl_conjugate_X
    (hdiamond : SimpleDiamondProducts P b)
    (i j : b.support) (hne : i ≠ j) (s t : R) :
    Commute (weightCompanionX P b O hc hm R i s)
      (weightCompanionWeyl P b O hc hm R i 1 *
        weightCompanionX P b O hc hm R j t *
          (weightCompanionWeyl P b O hc hm R i 1)⁻¹) := by
  have h := ((weightCompanionX_commute_Y P b hdiamond O hc hm R
    j i hne.symm t (-s)).symm).map
      (MulAut.conj (weightCompanionWeyl P b O hc hm R i 1)).toMonoidHom
  change Commute
    (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionY P b O hc hm R i (-s) *
      (weightCompanionWeyl P b O hc hm R i 1)⁻¹)
    (weightCompanionWeyl P b O hc hm R i 1 * weightCompanionX P b O hc hm R j t *
      (weightCompanionWeyl P b O hc hm R i 1)⁻¹) at h
  simpa only [weightCompanionWeyl_one_conjugate_Y_same, neg_neg] using h

end Atlas.Chevalley
