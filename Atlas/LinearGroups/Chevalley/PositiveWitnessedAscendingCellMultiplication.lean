import Atlas.GroupTheory.DoubleCosetProduct
import Atlas.LinearGroups.Chevalley.PositiveRootOmissionFactorization
import Atlas.LinearGroups.Chevalley.SimpleRootWeylCellReduction

/-! The ascending single-cell multiplication bound, retaining the actual positive-root hypothesis. -/
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

theorem weightCompanion_simple_B_N_mem_doubleCoset_of_positive
    (i : b.support) (n : weightCompanionExtendedWeylSubgroup P b O hc hm K)
    (hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm K n⁻¹ i.val))
    (g : WeightCompanion P b O hc hm K)
    (hg : g ∈ positiveWitnessedTorusJoin P b O hc hm K) :
    weightCompanionWeyl P b O hc hm K i 1 * g * n.val ∈
        DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1 * n.val)
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
  change s*g*n.val ∈ DoubleCoset.doubleCoset (s*n.val) B B
  rw [hfactor]
  exact Atlas.GroupTheory.doubleCoset_mul_left_right B (s*n.val)
    (weightCompanion_simple_X_N_mem_doubleCoset_of_positive P b O hc hm K i n hpos t)
    (s*v*s⁻¹) (n.val⁻¹*h*n.val) hleft hright

/-- The ascending case has one actual cell. No finite coefficient field or
Weyl-group recognition is used. -/
theorem positiveWitnessed_simple_doubleCoset_mul_weyl_subset_of_positive
    (i : b.support) (n : weightCompanionExtendedWeylSubgroup P b O hc hm K)
    (hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm K n⁻¹ i.val)) :
    DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) *
      DoubleCoset.doubleCoset n.val
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) ⊆
      DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1 * n.val)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  let s := weightCompanionWeyl P b O hc hm K i 1
  rintro g ⟨x, hx, y, hy, rfl⟩
  obtain ⟨a, ha, b', hb, hx⟩ := DoubleCoset.mem_doubleCoset.mp hx
  obtain ⟨c, hc', d, hd, hy⟩ := DoubleCoset.mem_doubleCoset.mp hy
  have he : x*y = a*(s*(b'*c)*n.val)*d := by
    dsimp only [s]
    rw [hx, hy]
    group
  change x*y ∈ DoubleCoset.doubleCoset (s*n.val) B B
  rw [he]
  exact Atlas.GroupTheory.doubleCoset_mul_left_right B (s*n.val)
    (weightCompanion_simple_B_N_mem_doubleCoset_of_positive
      P b O hc hm K hdiamond i n hpos (b'*c) (B.mul_mem hb hc')) a d ha hd

end Atlas.Chevalley
