import Atlas.GroupTheory.DoubleCosetMultiplication
import Atlas.LinearGroups.Chevalley.PositiveRootOmissionFactorization
import Atlas.LinearGroups.Chevalley.PositiveWitnessedRankOneCell
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSameRoot
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusNormalizer

/-! The actual simple-reflection double coset squares into B ∪ B n_i B.
The proof combines omitted-root factorization, actual torus normalization,
same-root Weyl exchange and the literal field rank-one identity. No Bruhat
decomposition, counting, BN-pair or global projection-kernel premise occurs. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
open scoped Pointwise

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K] (hdiamond : SimpleDiamondProducts P b)
include hdiamond

/-- Every actual middle sandwich n_i*b*n_i lies in one of the two rank-one
cells. The positive element is split at the omitted simple root only. -/
theorem weightCompanionWeyl_sandwich_mem_positiveWitnessed_or_doubleCoset
    (i : b.support) (g : WeightCompanion P b O hc hm K)
    (hg : g ∈ positiveWitnessedTorusJoin P b O hc hm K) :
    weightCompanionWeyl P b O hc hm K i 1 * g *
      weightCompanionWeyl P b O hc hm K i 1 ∈
        positiveWitnessedTorusJoin P b O hc hm K ∨
    weightCompanionWeyl P b O hc hm K i 1 * g *
      weightCompanionWeyl P b O hc hm K i 1 ∈
        DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
          (positiveWitnessedTorusJoin P b O hc hm K)
          (positiveWitnessedTorusJoin P b O hc hm K) := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  let U := positiveWitnessedWeightCompanionSubgroup P b O hc hm K
  let T := weightCompanionTorusSubgroup P b O hc hm K
  let n := weightCompanionWeyl P b O hc hm K i 1
  have hUB : U ≤ B := le_sup_left
  have hTB : T ≤ B := le_sup_right
  have hprod : g ∈ (U : Set (WeightCompanion P b O hc hm K)) *
      (T : Set (WeightCompanion P b O hc hm K)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U T
      (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm K)]
    exact hg
  obtain ⟨u,hu,h,hh,huh⟩ := hprod
  obtain ⟨v,hv,t,hvt⟩ := positiveWitnessed_exists_omission_mul_X
    P b O hc hm K hdiamond i u hu
  have hleft : n*v*n⁻¹ ∈ B := by
    apply hUB
    apply weightCompanionWeyl_conjugate_omission_le_witnessed
      P b O hc hm K hdiamond i
    change n*v*n⁻¹ ∈ (positiveRootOmissionSubgroup P b O hc hm K i).map
      (MulAut.conj n).toMonoidHom
    exact ⟨v,hv,rfl⟩
  have htorus : n*h*n⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp
      (weightCompanionWeyl_mem_torusNormalizer P b O hc hm K i) h).mp hh
  have hsquare : n^2 ∈ B := by
    rw [show n^2 = weightCompanionTorus P b O hc hm K i (-1) from
      weightCompanionWeyl_one_sq P b O hc hm K i]
    exact weightCompanionTorus_mem_positiveWitnessedTorusJoin P b O hc hm K i (-1)
  have hright : (n*h*n⁻¹)*n^2 ∈ B := B.mul_mem (hTB htorus) hsquare
  have hfactor : n*g*n = (n*v*n⁻¹) * weightCompanionY P b O hc hm K i (-t) *
      ((n*h*n⁻¹)*n^2) := by
    calc
      n*g*n = (n*v*n⁻¹) * (n*weightCompanionX P b O hc hm K i t*n⁻¹) *
          ((n*h*n⁻¹)*n^2) := by
        rw [← huh,← hvt]
        group
      _ = _ := by
        rw [weightCompanionWeyl_one_conjugate_X_same P b O hc hm K i t]
  change n*g*n ∈ B ∨ n*g*n ∈ DoubleCoset.doubleCoset n B B
  rw [hfactor]
  exact Atlas.GroupTheory.subgroup_or_doubleCoset_mul_left_right B n
    (weightCompanionY_mem_positiveWitnessed_or_doubleCoset P b O hc hm K i (-t))
    (n*v*n⁻¹) ((n*h*n⁻¹)*n^2) hleft hright

/-- The first actual Bruhat multiplication inclusion for the existing full
companion group: its simple-reflection cell squares into the two cells. -/
theorem positiveWitnessed_simple_doubleCoset_mul_self_subset (i : b.support) :
    DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) *
      DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) ⊆
      (positiveWitnessedTorusJoin P b O hc hm K : Set _) ∪
        DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
          (positiveWitnessedTorusJoin P b O hc hm K)
          (positiveWitnessedTorusJoin P b O hc hm K) :=
  Atlas.GroupTheory.doubleCoset_mul_self_subset_of_sandwich _ _
    (weightCompanionWeyl_sandwich_mem_positiveWitnessed_or_doubleCoset
      P b O hc hm K hdiamond i)

end Atlas.Chevalley
