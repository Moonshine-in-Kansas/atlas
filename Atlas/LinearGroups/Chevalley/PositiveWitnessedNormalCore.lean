import Atlas.GroupTheory.NormalDisjointNormalizer
import Atlas.LinearGroups.Chevalley.WeightCompanionFiniteCenter
import Atlas.LinearGroups.Chevalley.PositiveWitnessedRankOneCell
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSameRoot

/-! A normal subgroup contained in the actual Borel is central. Hence the
normal core of the Borel equals the entire center over finite fields.
This supplies the action-kernel calculation without a simplicity assumption. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule Atlas.GroupTheory RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

theorem weightCompanion_normal_le_torus_of_le_positiveJoin
    (hdiamond : SimpleDiamondProducts P b)
    (H : Subgroup (WeightCompanion P b O hc hm R)) [H.Normal]
    (hH : H ≤ positiveWitnessedTorusJoin P b O hc hm R) :
    H ≤ weightCompanionTorusSubgroup P b O hc hm R := by
  intro g hg
  apply mem_torus_of_mem_positiveWitnessed_and_opposite_join P b O hc hm R hdiamond g (hH hg)
  let n := (weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)).val
  have hn : n⁻¹ * g * n ∈ H := by
    simpa only [inv_inv] using (inferInstance : H.Normal).conj_mem g hg n⁻¹
  refine ⟨n⁻¹ * g * n, hH hn, ?_⟩
  change n * (n⁻¹ * g * n) * n⁻¹ = g
  group

theorem weightCompanion_normal_le_center_of_le_torus
    (hdiamond : SimpleDiamondProducts P b)
    (H : Subgroup (WeightCompanion P b O hc hm R)) [H.Normal]
    (hH : H ≤ weightCompanionTorusSubgroup P b O hc hm R) :
    H ≤ Subgroup.center (WeightCompanion P b O hc hm R) := by
  let U := positiveWitnessedWeightCompanionSubgroup P b O hc hm R
  have hn : H ≤ Subgroup.normalizer U := hH.trans
    (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)
  have hd : Disjoint H U := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro g ⟨hg, hu⟩
    exact Subgroup.mem_bot.mpr
      (positiveWitnessedWeightCompanion_eq_one_of_adjoint_diagonal P b O hc hm R hdiamond g hu
        (weightCompanionTorus_adjoint_offDiagonal_zero P b O hc hm R g (hH hg)))
  have hx (g : WeightCompanion P b O hc hm R) (hg : g ∈ H)
      (i : b.support) (t : R) : Commute g (weightCompanionX P b O hc hm R i t) :=
    normal_disjoint_normalizer_commute H U hn hd hg
      (weightCompanionX_mem_positiveWitnessed P b O hc hm R i t)
  intro g hg
  have hy (i : b.support) (t : R) : Commute g (weightCompanionY P b O hc hm R i t) := by
    let n := weightCompanionWeyl P b O hc hm R i 1
    have hng : n⁻¹ * g * n ∈ H := by
      simpa only [inv_inv] using (inferInstance : H.Normal).conj_mem g hg n⁻¹
    have hh := (hx _ hng i (-t)).map (MulAut.conj n).toMonoidHom
    change Commute (n * (n⁻¹ * g * n) * n⁻¹)
      (n * weightCompanionX P b O hc hm R i (-t) * n⁻¹) at hh
    have hfirst : n * (n⁻¹ * g * n) * n⁻¹ = g := by group
    rw [hfirst] at hh
    simpa only [n, weightCompanionWeyl_one_conjugate_X_same, neg_neg] using hh
  apply Subgroup.mem_center_iff.mpr
  intro z
  have hz : Commute g z := weightCompanion_induction P b O hc hm R (hx g hg) hy
    (Commute.one_right g) (fun _ _ h₁ h₂ => h₁.mul_right h₂)
    (fun _ h₁ => h₁.inv_right) z
  exact hz.eq.symm

theorem weightCompanion_normal_le_center_of_le_positiveJoin
    (hdiamond : SimpleDiamondProducts P b)
    (H : Subgroup (WeightCompanion P b O hc hm R)) [H.Normal]
    (hH : H ≤ positiveWitnessedTorusJoin P b O hc hm R) :
    H ≤ Subgroup.center (WeightCompanion P b O hc hm R) :=
  weightCompanion_normal_le_center_of_le_torus P b O hc hm R hdiamond H
    (weightCompanion_normal_le_torus_of_le_positiveJoin P b O hc hm R hdiamond H hH)

theorem positiveWitnessedTorusJoin_normalCore_eq_center
    (K : Type*) [Field K] [Finite K] [Fintype κ]
    (hdiamond : SimpleDiamondProducts P b) :
    (positiveWitnessedTorusJoin P b O hc hm K).normalCore =
      Subgroup.center (WeightCompanion P b O hc hm K) := by
  apply le_antisymm
  · exact weightCompanion_normal_le_center_of_le_positiveJoin P b O hc hm K hdiamond _
      (positiveWitnessedTorusJoin P b O hc hm K).normalCore_le
  · exact Subgroup.normal_le_normalCore.mpr
      (weightCompanion_center_le_positiveWitnessedTorusJoin P b O hc hm K hdiamond)

end Atlas.Chevalley
