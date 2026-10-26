import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusNormalizerIntersection
import Atlas.LinearGroups.Chevalley.PositiveWitnessedRankOneCell
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSameRoot
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionExchange
import Atlas.GroupTheory.LabelledSubgroupMarks

/-! A simple Weyl representative lies outside the actual B=U*T and does not
normalize B. These are direct statements on the concrete root-operator model;
no global Bruhat decomposition or group order is used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R] [Fintype κ]
  (hdiamond : SimpleDiamondProducts P b)
include hdiamond

/-- The simple reflection changes the sign of its own root, whereas the
actual B∩N is the root-action kernel T. -/
theorem weightCompanionWeyl_one_not_mem_positiveWitnessedTorusJoin
    (i : b.support) :
    weightCompanionWeyl P b O hc hm R i 1 ∉
      positiveWitnessedTorusJoin P b O hc hm R := by
  intro hb
  let n := weightCompanionSimpleWeylInN P b O hc hm R i
  have ht : n.val ∈ weightCompanionTorusSubgroup P b O hc hm R := by
    rw [← positiveWitnessedTorusJoin_inf_extendedWeyl_eq_torus P b O hc hm R hdiamond]
    exact ⟨hb,n.property⟩
  have hk : weightCompanionNRootPermHom P b O hc hm R n = 1 :=
    weightCompanionTorus_le_rootPermKer P b O hc hm R ht
  change weightCompanionNRootPermHom P b O hc hm R
    (weightCompanionSimpleWeylInN P b O hc hm R i) = 1 at hk
  rw [weightCompanionNRootPermHom_simple] at hk
  have he : P.reflectionPerm i.val i.val = i.val :=
    congrArg (fun w : Equiv.Perm ι => w i.val) hk
  apply not_isPos_reflection_simple P b i
  rw [he]
  exact b.isPos_of_mem_support i.property

/-- Conjugating B by n_i cannot stay inside B: that would put Y_i(-1),
and hence the literal word n_i=X_i(1)Y_i(-1)X_i(1), back in B. -/
theorem weightCompanionWeyl_conjugate_positiveWitnessedTorusJoin_not_le
    (i : b.support) :
    ¬ conjugateSubgroup (weightCompanionWeyl P b O hc hm R i 1)
        (positiveWitnessedTorusJoin P b O hc hm R) ≤
      positiveWitnessedTorusJoin P b O hc hm R := by
  intro h
  let B := positiveWitnessedTorusJoin P b O hc hm R
  let n := weightCompanionWeyl P b O hc hm R i 1
  have hx : weightCompanionX P b O hc hm R i 1 ∈ B :=
    weightCompanionX_mem_positiveWitnessedTorusJoin P b O hc hm R i 1
  have hy : weightCompanionY P b O hc hm R i (-1) ∈ B := by
    rw [← weightCompanionWeyl_one_conjugate_X_same P b O hc hm R i 1]
    apply h
    exact ⟨weightCompanionX P b O hc hm R i 1, hx, rfl⟩
  have hn : n ∈ B := by
    change weightCompanionX P b O hc hm R i 1 *
      weightCompanionY P b O hc hm R i (-1) *
        weightCompanionX P b O hc hm R i 1 ∈ B
    exact B.mul_mem (B.mul_mem hx hy) hx
  exact weightCompanionWeyl_one_not_mem_positiveWitnessedTorusJoin
    P b O hc hm R hdiamond i hn

end Atlas.Chevalley
