import Atlas.LinearGroups.Chevalley.WeightCompanionRootMarks
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusNormalizer
import Mathlib.Tactic.Group

/-! Exact parameter scaling by a Weyl square on a once-conjugated simple
root family. Only the existing literal Weyl/torus relations are used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule Atlas.GroupTheory
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- The coefficient is a unit, displayed before passing to subgroup ranges. -/
theorem weightCompanionWeyl_sq_conjugate_weyl_X (i j k : b.support) (t : R) :
    let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    let c : Rˣ := (-1) ^ (-b.cartanMatrix j i)
    let u : Rˣ := c ^ b.cartanMatrix k j * (-1) ^ b.cartanMatrix k i
    ni ^ 2 * (nj * weightCompanionX P b O hc hm R k t * nj⁻¹) * (ni ^ 2)⁻¹ =
      nj * weightCompanionX P b O hc hm R k (u.val * t) * nj⁻¹ := by
  dsimp only
  let nj := weightCompanionWeyl P b O hc hm R j 1
  let Ti := weightCompanionTorus P b O hc hm R i (-1)
  let c : Rˣ := (-1) ^ (-b.cartanMatrix j i)
  let Tj := weightCompanionTorus P b O hc hm R j c
  have hInv : nj⁻¹ * Ti * nj = Tj * Ti :=
    weightCompanionWeyl_inv_conjugate_Torus P b O hc hm R j i (-1)
  simp only [weightCompanionWeyl_one_sq]
  change Ti * (nj * weightCompanionX P b O hc hm R k t * nj⁻¹) * Ti⁻¹ = _
  calc
    _ = nj * ((nj⁻¹ * Ti * nj) * weightCompanionX P b O hc hm R k t *
        (nj⁻¹ * Ti * nj)⁻¹) * nj⁻¹ := by group
    _ = nj * (Tj * (Ti * weightCompanionX P b O hc hm R k t * Ti⁻¹) * Tj⁻¹) * nj⁻¹ := by
      rw [hInv]
      group
    _ = _ := by
      dsimp only [Ti, Tj]
      rw [weightCompanionTorus_conjugate_X_cross,
        weightCompanionTorus_conjugate_X_cross]
      simp only [Units.val_mul, mul_assoc, c, nj]

/-- The same square fixes the paired mark of a once-conjugated simple root.
This is proved before and independently of arbitrary-root coherence. -/
theorem weightCompanionRootMark_weyl_square_conjugate (i j k : b.support) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
      (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
        (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
          (weightCompanionSimpleRootMark P b O hc hm R k))) =
      labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
        (weightCompanionSimpleRootMark P b O hc hm R k) := by
  apply Prod.ext
  · exact P.reflectionPerm_self i.val (P.reflectionPerm j.val k.val)
  · let ni := weightCompanionWeyl P b O hc hm R i 1
    let nj := weightCompanionWeyl P b O hc hm R j 1
    let c : Rˣ := (-1) ^ (-b.cartanMatrix j i)
    let u : Rˣ := c ^ b.cartanMatrix k j * (-1) ^ b.cartanMatrix k i
    let f := (MulAut.conj nj).toMonoidHom.comp (weightCompanionXHom P b O hc hm R k)
    let e : Multiplicative R → Multiplicative R :=
      fun x => Multiplicative.ofAdd (u.val * x.toAdd)
    have he : Function.Surjective e := by
      intro x
      refine ⟨Multiplicative.ofAdd (u.inv * x.toAdd), ?_⟩
      change u.val * (u.inv * x.toAdd) = x.toAdd
      rw [← mul_assoc, u.val_inv, one_mul]
    have h : conjugateSubgroup (ni ^ 2) f.range = f.range := by
      apply conjugateSubgroup_range_eq_of_surjective _ _ _ e he
      intro x
      exact weightCompanionWeyl_sq_conjugate_weyl_X P b O hc hm R i j k x.toAdd
    change conjugateSubgroup ni (conjugateSubgroup ni
      (conjugateSubgroup nj (weightCompanionXHom P b O hc hm R k).range)) =
        conjugateSubgroup nj (weightCompanionXHom P b O hc hm R k).range
    rw [← conjugateSubgroup_mul, ← pow_two]
    simpa only [conjugateSubgroup_range, f] using h

end Atlas.Chevalley
