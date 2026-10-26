import Atlas.LinearGroups.Chevalley.PositiveWitnessedWeylCellDisjointness
import Atlas.LinearGroups.Chevalley.PositiveWitnessedWeylCellCoverage
import Mathlib.Data.Set.Lattice

/-! The actual full companion is a disjoint union of double cells indexed by
the existing root-permutation Weyl group. This is an equivalence with the
literal cell fibers, not a parameterization or cardinality formula for them. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K]

/-- The literal double cell of the established chosen N lift. Independence
from this representative is proved next rather than built into the definition. -/
def positiveWitnessedWeylCell (w : P.weylGroupToPerm.range) :
    Set (WeightCompanion P b O hc hm K) :=
  DoubleCoset.doubleCoset (weightCompanionTitsLift P b O hc hm K w).val
    (positiveWitnessedTorusJoin P b O hc hm K) (positiveWitnessedTorusJoin P b O hc hm K)

variable [Fintype κ]

theorem positiveWitnessedWeylCell_eq_of_lift
    (hdiamond : SimpleDiamondProducts P b)
    (w : P.weylGroupToPerm.range)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm K)
    (hn : weightCompanionNRootPermHom P b O hc hm K n = w.val) :
    DoubleCoset.doubleCoset n.val
        (positiveWitnessedTorusJoin P b O hc hm K) (positiveWitnessedTorusJoin P b O hc hm K) =
      positiveWitnessedWeylCell P b O hc hm K w := by
  apply (weightCompanionN_doubleCoset_eq_iff_rootPerm_eq
    P b O hc hm K hdiamond n (weightCompanionTitsLift P b O hc hm K w)).mpr
  exact hn.trans (weightCompanionNRootPermHom_titsLift P b O hc hm K w).symm

theorem positiveWitnessedWeylCell_disjoint
    (hdiamond : SimpleDiamondProducts P b)
    (w v : P.weylGroupToPerm.range) (hne : w ≠ v) :
    Disjoint (positiveWitnessedWeylCell P b O hc hm K w)
      (positiveWitnessedWeylCell P b O hc hm K v) := by
  apply weightCompanionN_doubleCosets_disjoint_of_rootPerm_ne P b O hc hm K hdiamond
  intro he
  rw [weightCompanionNRootPermHom_titsLift,weightCompanionNRootPermHom_titsLift] at he
  exact hne (Subtype.ext he)

theorem exists_mem_positiveWitnessedWeylCell
    (hdiamond : SimpleDiamondProducts P b) (g : WeightCompanion P b O hc hm K) :
    ∃ w : P.weylGroupToPerm.range, g ∈ positiveWitnessedWeylCell P b O hc hm K w := by
  obtain ⟨n,hn⟩ := weightCompanion_mem_positiveWitnessedWeylCells P b O hc hm K hdiamond g
  let w : P.weylGroupToPerm.range :=
    ⟨weightCompanionNRootPermHom P b O hc hm K n,
      simpleRootPermutationSubgroup_le_weylImage P b
        (weightCompanionNRootPerm_spec P b O hc hm K n).1⟩
  refine ⟨w,?_⟩
  rw [← positiveWitnessedWeylCell_eq_of_lift P b O hc hm K hdiamond w n rfl]
  exact hn

theorem existsUnique_mem_positiveWitnessedWeylCell
    (hdiamond : SimpleDiamondProducts P b) (g : WeightCompanion P b O hc hm K) :
    ∃! w : P.weylGroupToPerm.range, g ∈ positiveWitnessedWeylCell P b O hc hm K w := by
  obtain ⟨w,hw⟩ := exists_mem_positiveWitnessedWeylCell P b O hc hm K hdiamond g
  refine ⟨w,hw,?_⟩
  intro v hv
  by_contra hne
  exact Set.disjoint_left.mp
    (positiveWitnessedWeylCell_disjoint P b O hc hm K hdiamond v w hne) hv hw

theorem positiveWitnessedWeylCell_iUnion
    (hdiamond : SimpleDiamondProducts P b) :
    (⋃ w : P.weylGroupToPerm.range, positiveWitnessedWeylCell P b O hc hm K w) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  exact Set.mem_iUnion.mpr (exists_mem_positiveWitnessedWeylCell P b O hc hm K hdiamond g)

/-- The disjoint union of actual cell fibers is the actual full companion.
This equivalence does not replace any fiber by an unproved coordinate space. -/
def positiveWitnessedWeylCellSigmaEquiv
    (hdiamond : SimpleDiamondProducts P b) :
    (Σ w : P.weylGroupToPerm.range, positiveWitnessedWeylCell P b O hc hm K w) ≃
      WeightCompanion P b O hc hm K :=
  Set.sigmaEquiv (positiveWitnessedWeylCell P b O hc hm K)
    (existsUnique_mem_positiveWitnessedWeylCell P b O hc hm K hdiamond)

theorem positiveWitnessedWeylCellSigmaEquiv_apply
    (hdiamond : SimpleDiamondProducts P b)
    (x : Σ w : P.weylGroupToPerm.range, positiveWitnessedWeylCell P b O hc hm K w) :
    positiveWitnessedWeylCellSigmaEquiv P b O hc hm K hdiamond x = x.2.val := rfl

end Atlas.Chevalley
