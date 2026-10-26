import Atlas.GroupTheory.DoubleCosetWordSeparation
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusNormalizerIntersection
import Atlas.LinearGroups.Chevalley.PositiveWitnessedWeylCellMultiplication
import Atlas.LinearGroups.Chevalley.WeightCompanionTitsLift

/-! Distinct actual Weyl actions give disjoint B-N-B cells. The proof uses
B intersect N = T, the proved simple two-cell multiplication bound, and ordinary
simple-word induction. It does not use Bruhat coverage, cell counts, the full
adjoint kernel, or positive-root coordinate collection. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData
open Atlas.GroupTheory.ReducedWords
open scoped Pointwise

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K] [Fintype κ]

private theorem positiveWitnessed_N_action_eq_one_iff
    (hdiamond : SimpleDiamondProducts P b)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm K) :
    weightCompanionNRootPermHom P b O hc hm K n = 1 ↔
      n.val ∈ positiveWitnessedTorusJoin P b O hc hm K := by
  constructor
  · intro he
    have hk : n ∈ (weightCompanionNRootPermHom P b O hc hm K).ker := he
    rw [weightCompanionNRootPermHom_ker_eq_torus P b O hc hm K hdiamond] at hk
    exact (show weightCompanionTorusSubgroup P b O hc hm K ≤
      positiveWitnessedTorusJoin P b O hc hm K from le_sup_right) hk
  · intro hb
    have ht : n.val ∈ weightCompanionTorusSubgroup P b O hc hm K := by
      rw [← positiveWitnessedTorusJoin_inf_extendedWeyl_eq_torus P b O hc hm K hdiamond]
      exact ⟨hb,n.property⟩
    have hk : n ∈ (weightCompanionNRootPermHom P b O hc hm K).ker := by
      rw [weightCompanionNRootPermHom_ker_eq_torus P b O hc hm K hdiamond]
      exact ht
    exact hk

private theorem positiveWitnessed_N_simple_words
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm K) :
    ∃ l : List b.support,
      weightCompanionNRootPermHom P b O hc hm K
        ((l.map (weightCompanionSimpleWeylInN P b O hc hm K)).prod) =
      weightCompanionNRootPermHom P b O hc hm K n := by
  let w : P.weylGroupToPerm.range :=
    ⟨weightCompanionNRootPermHom P b O hc hm K n,
      simpleRootPermutationSubgroup_le_weylImage P b
        (weightCompanionNRootPerm_spec P b O hc hm K n).1⟩
  obtain ⟨l,hl,hred⟩ := root_reduced_representatives P b w
  refine ⟨l,?_⟩
  change weightCompanionNRootPermHom P b O hc hm K
    (wordEval (weightCompanionSimpleWeylInN P b O hc hm K) l) = w.val
  rw [weightCompanionNRootPermHom_wordEval]
  exact congrArg Subtype.val hl

/-- Membership in an N-indexed double cell is exactly equality of the
already defined root-permutation actions. -/
theorem weightCompanionN_mem_doubleCoset_iff_rootPerm_eq
    (hdiamond : SimpleDiamondProducts P b)
    (n m : weightCompanionExtendedWeylSubgroup P b O hc hm K) :
    n.val ∈ DoubleCoset.doubleCoset m.val
      (positiveWitnessedTorusJoin P b O hc hm K) (positiveWitnessedTorusJoin P b O hc hm K) ↔
      weightCompanionNRootPermHom P b O hc hm K n =
        weightCompanionNRootPermHom P b O hc hm K m := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  let N₀ := weightCompanionExtendedWeylSubgroup P b O hc hm K
  let φ := weightCompanionNRootPermHom P b O hc hm K
  let σ := weightCompanionSimpleWeylInN P b O hc hm K
  have hk := positiveWitnessed_N_action_eq_one_iff P b O hc hm K hdiamond
  constructor
  · intro h
    apply Atlas.GroupTheory.N_action_eq_of_mem_doubleCoset_of_simple_words B N₀ φ σ hk
      (fun i => ?_) (fun i v => ?_) (positiveWitnessed_N_simple_words P b O hc hm K) n m h
    · change weightCompanionWeyl P b O hc hm K i 1 ^ 2 ∈ B
      rw [weightCompanionWeyl_one_sq]
      exact weightCompanionTorus_mem_positiveWitnessedTorusJoin P b O hc hm K i (-1)
    · exact positiveWitnessed_simple_doubleCoset_mul_weyl_subset P b O hc hm K hdiamond i v
  · exact Atlas.GroupTheory.N_mem_doubleCoset_of_action_eq B N₀ φ hk n m

theorem weightCompanionN_doubleCoset_eq_iff_rootPerm_eq
    (hdiamond : SimpleDiamondProducts P b)
    (n m : weightCompanionExtendedWeylSubgroup P b O hc hm K) :
    DoubleCoset.doubleCoset n.val
        (positiveWitnessedTorusJoin P b O hc hm K) (positiveWitnessedTorusJoin P b O hc hm K) =
      DoubleCoset.doubleCoset m.val
        (positiveWitnessedTorusJoin P b O hc hm K) (positiveWitnessedTorusJoin P b O hc hm K) ↔
      weightCompanionNRootPermHom P b O hc hm K n =
        weightCompanionNRootPermHom P b O hc hm K m := by
  constructor
  · intro h
    apply (weightCompanionN_mem_doubleCoset_iff_rootPerm_eq P b O hc hm K hdiamond n m).mp
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem
      ((weightCompanionN_mem_doubleCoset_iff_rootPerm_eq P b O hc hm K hdiamond n m).mpr h)

theorem weightCompanionN_doubleCosets_disjoint_of_rootPerm_ne
    (hdiamond : SimpleDiamondProducts P b)
    (n m : weightCompanionExtendedWeylSubgroup P b O hc hm K)
    (hne : weightCompanionNRootPermHom P b O hc hm K n ≠
      weightCompanionNRootPermHom P b O hc hm K m) :
    Disjoint (DoubleCoset.doubleCoset n.val
        (positiveWitnessedTorusJoin P b O hc hm K) (positiveWitnessedTorusJoin P b O hc hm K))
      (DoubleCoset.doubleCoset m.val
        (positiveWitnessedTorusJoin P b O hc hm K) (positiveWitnessedTorusJoin P b O hc hm K)) := by
  by_contra h
  have hm' := DoubleCoset.mem_doubleCoset_of_not_disjoint h
  exact hne ((weightCompanionN_mem_doubleCoset_iff_rootPerm_eq
    P b O hc hm K hdiamond m n).mp hm').symm

end Atlas.Chevalley
