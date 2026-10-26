import Atlas.LinearGroups.Chevalley.WeightCompanionLeftInduction
import Atlas.LinearGroups.Chevalley.PositiveWitnessedWeylCellMultiplication

/-! Coverage by B*n*B for the actual full companion, with n in the actual N.
The union is preserved under each literal root generator. No subgroup closure
of the union, Bruhat uniqueness, cell disjointness or counting is assumed. -/
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
  (K : Type*) [Field K]

/-- The union indexed by the existing actual subgroup N. Distinct indices
are not asserted to define distinct double cosets. -/
def positiveWitnessedWeylCells : Set (WeightCompanion P b O hc hm K) :=
  {g | ∃ n : weightCompanionExtendedWeylSubgroup P b O hc hm K,
    g ∈ DoubleCoset.doubleCoset n.val
      (positiveWitnessedTorusJoin P b O hc hm K)
      (positiveWitnessedTorusJoin P b O hc hm K)}

theorem one_mem_positiveWitnessedWeylCells :
    (1 : WeightCompanion P b O hc hm K) ∈ positiveWitnessedWeylCells P b O hc hm K :=
  ⟨1,DoubleCoset.mem_doubleCoset_self _ _ _⟩

theorem positiveWitnessedWeylCells_mul_left_of_mem_B
    (a g : WeightCompanion P b O hc hm K)
    (ha : a ∈ positiveWitnessedTorusJoin P b O hc hm K)
    (hg : g ∈ positiveWitnessedWeylCells P b O hc hm K) :
    a*g ∈ positiveWitnessedWeylCells P b O hc hm K := by
  obtain ⟨n,hn⟩ := hg
  refine ⟨n,?_⟩
  simpa only [mul_one] using Atlas.GroupTheory.doubleCoset_mul_left_right
    (positiveWitnessedTorusJoin P b O hc hm K) n.val hn a 1 ha
    (positiveWitnessedTorusJoin P b O hc hm K).one_mem

variable (hdiamond : SimpleDiamondProducts P b)
include hdiamond

theorem positiveWitnessedWeylCells_mul_left_of_mem_simple_cell
    (i : b.support) (a g : WeightCompanion P b O hc hm K)
    (ha : a ∈ DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
      (positiveWitnessedTorusJoin P b O hc hm K)
      (positiveWitnessedTorusJoin P b O hc hm K))
    (hg : g ∈ positiveWitnessedWeylCells P b O hc hm K) :
    a*g ∈ positiveWitnessedWeylCells P b O hc hm K := by
  obtain ⟨n,hn⟩ := hg
  have hprod := positiveWitnessed_simple_doubleCoset_mul_weyl_subset
    P b O hc hm K hdiamond i n (show a*g ∈ _ from ⟨a,ha,g,hn,rfl⟩)
  rcases hprod with h | h
  · exact ⟨weightCompanionSimpleWeylInN P b O hc hm K i * n,h⟩
  · exact ⟨n,h⟩

/-- Actual Bruhat coverage: every element of the originally generated full
companion belongs to B*n*B for some literal n in the existing N. -/
theorem weightCompanion_mem_positiveWitnessedWeylCells
    (g : WeightCompanion P b O hc hm K) :
    g ∈ positiveWitnessedWeylCells P b O hc hm K := by
  apply weightCompanion_induction_left P b O hc hm K
  · exact one_mem_positiveWitnessedWeylCells P b O hc hm K
  · intro i t g hg
    exact positiveWitnessedWeylCells_mul_left_of_mem_B P b O hc hm K
      (weightCompanionX P b O hc hm K i t) g
      (weightCompanionX_mem_positiveWitnessedTorusJoin P b O hc hm K i t) hg
  · intro i t g hg
    rcases weightCompanionY_mem_positiveWitnessed_or_doubleCoset
      P b O hc hm K i t with hB | hcell
    · exact positiveWitnessedWeylCells_mul_left_of_mem_B P b O hc hm K
        (weightCompanionY P b O hc hm K i t) g hB hg
    · exact positiveWitnessedWeylCells_mul_left_of_mem_simple_cell P b O hc hm K hdiamond
        i (weightCompanionY P b O hc hm K i t) g hcell hg

theorem positiveWitnessedWeylCells_eq_univ :
    positiveWitnessedWeylCells P b O hc hm K = Set.univ := by
  apply Set.eq_univ_of_forall
  exact weightCompanion_mem_positiveWitnessedWeylCells P b O hc hm K hdiamond

/-- Literal B-N-B factorization, without a uniqueness assertion. -/
theorem weightCompanion_exists_positiveWitnessed_mul_N_mul
    (g : WeightCompanion P b O hc hm K) :
    ∃ (n : weightCompanionExtendedWeylSubgroup P b O hc hm K)
      (a c : WeightCompanion P b O hc hm K),
      a ∈ positiveWitnessedTorusJoin P b O hc hm K ∧
      c ∈ positiveWitnessedTorusJoin P b O hc hm K ∧ g = a*n.val*c := by
  obtain ⟨n,hn⟩ := weightCompanion_mem_positiveWitnessedWeylCells P b O hc hm K hdiamond g
  obtain ⟨a,ha,c,hc',he⟩ := DoubleCoset.mem_doubleCoset.mp hn
  exact ⟨n,a,c,ha,hc',he⟩

end Atlas.Chevalley
