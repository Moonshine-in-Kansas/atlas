import Atlas.GroupTheory.DoubleCosetProduct
import Atlas.LinearGroups.Chevalley.PositiveRootOmissionFactorization
import Atlas.LinearGroups.Chevalley.SimpleRootWeylCellReduction

/-! Multiplication by a simple-reflection cell, for every actual element of N.
This supplies the structural two-cell bound before any global Bruhat covering,
disjointness, counting or BN-pair construction. -/
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

theorem weightCompanion_simple_B_N_mem_doubleCosets
    (i : b.support) (n : weightCompanionExtendedWeylSubgroup P b O hc hm K)
    (g : WeightCompanion P b O hc hm K)
    (hg : g ∈ positiveWitnessedTorusJoin P b O hc hm K) :
    weightCompanionWeyl P b O hc hm K i 1 * g * n.val ∈
        DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1 * n.val)
          (positiveWitnessedTorusJoin P b O hc hm K)
          (positiveWitnessedTorusJoin P b O hc hm K) ∨
    weightCompanionWeyl P b O hc hm K i 1 * g * n.val ∈
        DoubleCoset.doubleCoset n.val
          (positiveWitnessedTorusJoin P b O hc hm K)
          (positiveWitnessedTorusJoin P b O hc hm K) := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  let U := positiveWitnessedWeightCompanionSubgroup P b O hc hm K
  let T := weightCompanionTorusSubgroup P b O hc hm K
  let s := weightCompanionWeyl P b O hc hm K i 1
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
  have hleft : s*v*s⁻¹ ∈ B := by
    apply hUB
    apply weightCompanionWeyl_conjugate_omission_le_witnessed
      P b O hc hm K hdiamond i
    change s*v*s⁻¹ ∈ (positiveRootOmissionSubgroup P b O hc hm K i).map
      (MulAut.conj s).toMonoidHom
    exact ⟨v,hv,rfl⟩
  have hright : n.val⁻¹*h*n.val ∈ B := by
    apply hTB
    exact (Subgroup.mem_normalizer_iff''.mp
      (weightCompanionExtendedWeylSubgroup_le_torusNormalizer
        P b O hc hm K n.property) h).mp hh
  have hfactor : s*g*n.val = (s*v*s⁻¹) *
      (s*weightCompanionX P b O hc hm K i t*n.val) * (n.val⁻¹*h*n.val) := by
    rw [← huh,← hvt]
    group
  change s*g*n.val ∈ DoubleCoset.doubleCoset (s*n.val) B B ∨
    s*g*n.val ∈ DoubleCoset.doubleCoset n.val B B
  rw [hfactor]
  rcases weightCompanion_simple_X_N_mem_doubleCosets P b O hc hm K i n t with hcell | hcell
  · exact Or.inl (Atlas.GroupTheory.doubleCoset_mul_left_right B (s*n.val)
      hcell (s*v*s⁻¹) (n.val⁻¹*h*n.val) hleft hright)
  · exact Or.inr (Atlas.GroupTheory.doubleCoset_mul_left_right B n.val
      hcell (s*v*s⁻¹) (n.val⁻¹*h*n.val) hleft hright)

/-- The actual two-cell simple-reflection multiplication bound. The second
representative is any literal element of N, not a new abstract Weyl model. -/
theorem positiveWitnessed_simple_doubleCoset_mul_weyl_subset
    (i : b.support) (n : weightCompanionExtendedWeylSubgroup P b O hc hm K) :
    DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) *
      DoubleCoset.doubleCoset n.val
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) ⊆
      DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1 * n.val)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) ∪
      DoubleCoset.doubleCoset n.val
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) :=
  Atlas.GroupTheory.doubleCoset_mul_subset_of_sandwich _ _ _
    (weightCompanion_simple_B_N_mem_doubleCosets P b O hc hm K hdiamond i n)

end Atlas.Chevalley
