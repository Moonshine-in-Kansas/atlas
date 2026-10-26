import Atlas.GroupTheory.NormalizerJoin
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusNormalization
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusIntersection

/-! The join of the all-witness positive subgroup and the actual torus is their
internal semidirect product. This does not assert ordered root collection or a
Bruhat decomposition of the whole Chevalley group. -/

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
  (R : Type*) [CommRing R] [Nontrivial R]

/-- The actual join of the witnessed positive subgroup with the torus. -/
def positiveWitnessedTorusJoin : Subgroup (WeightCompanion P b O hc hm R) :=
  positiveWitnessedWeightCompanionSubgroup P b O hc hm R ⊔
    weightCompanionTorusSubgroup P b O hc hm R

/-- The witnessed positive subgroup is normal in this join. -/
theorem positiveWitnessed_normal_in_torusJoin :
    ((positiveWitnessedWeightCompanionSubgroup P b O hc hm R).subgroupOf
      (positiveWitnessedTorusJoin P b O hc hm R)).Normal :=
  Atlas.GroupTheory.normalizerJoin_normal _ _
    (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)

/-- Conjugation by the actual torus gives the semidirect-product action. -/
def positiveWitnessedTorusAction :
    weightCompanionTorusSubgroup P b O hc hm R →*
      MulAut (positiveWitnessedWeightCompanionSubgroup P b O hc hm R) :=
  (positiveWitnessedWeightCompanionSubgroup P b O hc hm R).normalizerMonoidHom.comp
    (Subgroup.inclusion
      (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R))

variable [Fintype κ]

/-- The actual join is isomorphic to U semidirect T, with the conjugation action.
The diamond hypothesis is used only through the proved trivial intersection. -/
def positiveWitnessedTorusJoinMulEquiv (hdiamond : SimpleDiamondProducts P b) :
    positiveWitnessedWeightCompanionSubgroup P b O hc hm R ⋊[
      positiveWitnessedTorusAction P b O hc hm R]
      weightCompanionTorusSubgroup P b O hc hm R ≃*
        positiveWitnessedTorusJoin P b O hc hm R :=
  Atlas.GroupTheory.normalizerJoinMulEquiv _ _
    (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)
    (disjoint_iff.mpr
      (positiveWitnessedWeightCompanion_inf_torus_eq_bot P b O hc hm R hdiamond))

theorem positiveWitnessedTorusJoinMulEquiv_apply (hdiamond : SimpleDiamondProducts P b)
    (x : positiveWitnessedWeightCompanionSubgroup P b O hc hm R ⋊[
      positiveWitnessedTorusAction P b O hc hm R]
      weightCompanionTorusSubgroup P b O hc hm R) :
    (positiveWitnessedTorusJoinMulEquiv P b O hc hm R hdiamond x :
      WeightCompanion P b O hc hm R) = (x.left : WeightCompanion P b O hc hm R) *
        x.right := rfl

/-- Unique U*T factorization concerns these two whole factors, not coordinates
in a prescribed ordered product of positive root groups. -/
theorem positiveWitnessedTorusJoin_existsUnique (hdiamond : SimpleDiamondProducts P b)
    (g : positiveWitnessedTorusJoin P b O hc hm R) :
    ∃! p : positiveWitnessedWeightCompanionSubgroup P b O hc hm R ×
      weightCompanionTorusSubgroup P b O hc hm R,
      (p.1 : WeightCompanion P b O hc hm R) * p.2 = g.val :=
  Atlas.GroupTheory.normalizerJoin_existsUnique _ _
    (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)
    (disjoint_iff.mpr
      (positiveWitnessedWeightCompanion_inf_torus_eq_bot P b O hc hm R hdiamond)) g

end Atlas.Chevalley
