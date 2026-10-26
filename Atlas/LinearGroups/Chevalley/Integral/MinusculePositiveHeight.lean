import Atlas.LinearGroups.Chevalley.Integral.MinusculeOrbitRepresentation
import Atlas.LinearGroups.Chevalley.Integral.GradedMatrix

/-! An integral minuscule weight height from the sum of positive coroots.
All scalar cancellation is in the integers. No inverse Cartan matrix or
coefficient-ring characteristic assumption is introduced. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Positive coroot labels, with positivity taken in the actual dual base. -/
def positiveCorootIndices : Finset ι := Finset.univ.filter b.flip.IsPos

/-- The literal integral sum of positive coroots, usually denoted 2ρ∨. -/
def twiceRhoCoroot : CorootLattice P :=
  ∑ j ∈ positiveCorootIndices P b, corootElement P j

/-- Every actual integral weight evaluates on the integral sum of positive coroots. -/
def weightHeight (μ : WeightLattice P) : ℤ := μ (twiceRhoCoroot P b)

private theorem positiveCorootErase_reflection_mem (i : b.support) (j : ι)
    (hj : j ∈ (positiveCorootIndices P b).erase i.val) :
    P.reflectionPerm i.val j ∈ (positiveCorootIndices P b).erase i.val := by
  -- These instances are consequences of the existing perfect root pairing,
  -- not extra assumptions about the ambient coroot group.
  letI : Module.IsReflexive ℤ M :=
    Module.IsReflexive.of_isPerfPair P.toLinearMap
  letI : Module.IsTorsionFree ℤ M := inferInstance
  letI : Module.IsReflexive ℤ N :=
    Module.IsReflexive.of_isPerfPair P.flip.toLinearMap
  letI : Module.IsTorsionFree ℤ N := inferInstance
  letI : P.flip.IsReduced := inferInstance
  obtain ⟨hji, hjpos⟩ := Finset.mem_erase.mp hj
  have hp : b.flip.IsPos j := (Finset.mem_filter.mp hjpos).2
  have hrpos : b.flip.IsPos (P.reflectionPerm i.val j) := by
    exact hp.reflectionPerm i.property hji
  have hne : P.reflectionPerm i.val j ≠ i.val := by
    intro he
    have hjneg : j = P.reflectionPerm i.val i.val := by
      calc
        j = P.reflectionPerm i.val (P.reflectionPerm i.val j) :=
          (P.reflectionPerm_self i.val j).symm
        _ = P.reflectionPerm i.val i.val := congrArg (P.reflectionPerm i.val) he
    have hiheight : b.flip.height i.val = 1 :=
      RootPairing.Base.height_one_of_mem_support (b := b.flip) i.property
    have hh : b.flip.height (P.reflectionPerm i.val i.val) = -1 := by
      simpa only [RootPairing.indexNeg_neg, RootPairing.flip_reflectionPerm,
        hiheight] using
          b.flip.height_reflectionPerm_self i.val
    have hp' : 0 < b.flip.height j := hp
    rw [hjneg, hh] at hp'
    omega
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrpos⟩⟩

/-- The positive-coroot pairing sum of each actual simple root is exactly two.
The proof pairs all other positive coroots under the simple reflection. -/
theorem simpleRoot_pairing_sum_positiveCoroots (i : b.support) :
    (∑ j ∈ positiveCorootIndices P b, P.pairing i.val j) = 2 := by
  let s := (positiveCorootIndices P b).erase i.val
  have hs : (∑ j ∈ s, P.pairing i.val j) = ∑ j ∈ s, -P.pairing i.val j := by
    refine Finset.sum_nbij' (P.reflectionPerm i.val) (P.reflectionPerm i.val)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      exact positiveCorootErase_reflection_mem P b i j hj
    · intro j hj
      exact positiveCorootErase_reflection_mem P b i j hj
    · intro j hj
      exact P.reflectionPerm_self i.val j
    · intro j hj
      exact P.reflectionPerm_self i.val j
    · intro j hj
      rw [P.pairing_reflectionPerm, P.pairing_reflectionPerm_self_left, neg_neg]
  rw [Finset.sum_neg_distrib] at hs
  have hz : (∑ j ∈ s, P.pairing i.val j) = 0 := by omega
  have hi : i.val ∈ positiveCorootIndices P b :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.flip.isPos_of_mem_support i.property⟩
  have he := Finset.add_sum_erase (positiveCorootIndices P b)
    (fun j => P.pairing i.val j) hi
  change P.pairing i.val i.val + (∑ j ∈ s, P.pairing i.val j) = _ at he
  rw [P.pairing_same, hz, add_zero] at he
  exact he.symm

/-- Each simple-root shift has degree two in this integral weight height. -/
theorem weightHeight_simpleRoot (i : b.support) :
    weightHeight P b (rootWeight P i.val) = 2 := by
  simpa only [weightHeight, twiceRhoCoroot, map_sum, rootWeight_corootElement] using
    simpleRoot_pairing_sum_positiveCoroots P b i

theorem weightHeight_add_simpleRoot (μ : WeightLattice P) (i : b.support) :
    weightHeight P b (μ + rootWeight P i.val) = weightHeight P b μ + 2 := by
  change (μ + rootWeight P i.val) (twiceRhoCoroot P b) = _
  rw [LinearMap.add_apply]
  change weightHeight P b μ + weightHeight P b (rootWeight P i.val) = _
  rw [weightHeight_simpleRoot]

/-- Exact simple-reflection change in integral height. -/
theorem weightHeight_reflection_simple (μ : WeightLattice P) (i : b.support) :
    weightHeight P b (weightReflection P i.val μ) =
      weightHeight P b μ - μ (corootElement P i.val) * 2 := by
  have hr : rootWeight P i.val (twiceRhoCoroot P b) = 2 :=
    weightHeight_simpleRoot P b i
  simp only [weightHeight, weightReflection_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hr]

/-- The actual integral minuscule simple raising matrix has degree two.
This is an operator support theorem, not a whole-group triangularity assertion. -/
theorem weightOrbit_raising_weightHeight_weightedSupport
    (S : Finset (WeightLattice P))
    (hclosed : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
    (hmin : ∀ μ ∈ S, ∀ i,
      μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
        μ (corootElement P i) = 1)
    (i : b.support) :
    WeightedSupport (fun μ : WeightOrbit P S => weightHeight P b μ.val) 2
      ((stringsOfWeightOrbit P S hclosed hmin).stepMatrix ℤ i.val (-1)) := by
  intro μ ν hne
  rw [weightOrbit_stepMatrix_entry] at hne
  have hs : ν.val (corootElement P i.val) = -1 ∧
      weightReflection P i.val ν.val = μ.val := by
    by_contra hs
    simp only [if_neg hs] at hne
    exact hne rfl
  obtain ⟨hgrade, hweight⟩ := hs
  change weightHeight P b μ.val = weightHeight P b ν.val + 2
  rw [← hweight, weightHeight_reflection_simple, hgrade]
  ring

end Atlas.Chevalley.Integral.Minuscule
