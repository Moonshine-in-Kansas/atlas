import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeightLattice
import Mathlib.LinearAlgebra.Pi

/-! Exact Dynkin labels as coordinates on the
actual coroot-dual weight lattice; no orbit or minuscule claim assumed. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) (b : P.Base) {n : ℕ} (e : Fin n ≃ b.support)

/-- Fundamental-weight coordinates indexed by the supplied actual simple-base equivalence. -/
def indexedWeightCoordinates : WeightLattice P ≃ₗ[ℤ] (Fin n → ℤ) :=
  (weightCoordinates P b).trans (LinearEquiv.funCongrLeft ℤ ℤ e)

/-- An integral Dynkin-label vector denotes an actual weight, not a new abstract model. -/
def weightOfLabels : (Fin n → ℤ) ≃ₗ[ℤ] WeightLattice P :=
  (indexedWeightCoordinates P b e).symm

@[simp] theorem indexedWeightCoordinates_apply (μ : WeightLattice P) (i : Fin n) :
    indexedWeightCoordinates P b e μ i = μ (corootBasis P b (e i)) := by
  exact weightCoordinates_apply P b μ (e i)

@[simp] theorem weightOfLabels_simple_evaluation (v : Fin n → ℤ) (i : Fin n) :
    weightOfLabels P b e v (corootBasis P b (e i)) = v i := by
  simpa only [indexedWeightCoordinates_apply, weightOfLabels] using
    congrFun ((indexedWeightCoordinates P b e).apply_symm_apply v) i

@[simp] theorem weightOfLabels_indexedCoordinates (μ : WeightLattice P) :
    weightOfLabels P b e (indexedWeightCoordinates P b e μ) = μ :=
  (indexedWeightCoordinates P b e).symm_apply_apply μ

/-- The chosen coordinate unit really is the corresponding fundamental weight. -/
theorem weightOfLabels_single (i : Fin n) :
    weightOfLabels P b e (Pi.single i 1) = fundamentalWeights P b (e i) := by
  apply (indexedWeightCoordinates P b e).injective
  funext j
  simp only [indexedWeightCoordinates_apply, weightOfLabels_simple_evaluation,
    fundamentalWeights_pairing]
  simp [Pi.single_apply, e.injective.eq_iff]

/-- Any supplied coroot-basis expansion computes the exact all-root grade. -/
theorem weightOfLabels_coroot_evaluation (v c : Fin n → ℤ) (a : ι)
    (hc : corootElement P a = ∑ i : Fin n, c i • corootBasis P b (e i)) :
    weightOfLabels P b e v (corootElement P a) = ∑ i, v i * c i := by
  rw [hc, map_sum]
  simp only [map_smul, smul_eq_mul, weightOfLabels_simple_evaluation, mul_comm]

variable [P.IsCrystallographic]

omit [P.IsCrystallographic] in
theorem indexedRootWeight_coordinates (a : ι) (i : Fin n) :
    indexedWeightCoordinates P b e (rootWeight P a) i = P.pairing a (e i) :=
  rootWeight_coordinates P b a (e i)

theorem indexedSimpleRootWeight_coordinates (i j : Fin n) :
    indexedWeightCoordinates P b e (rootWeight P (e i)) j = b.cartanMatrix (e i) (e j) :=
  simpleRootWeight_coordinates P b (e i) (e j)

/-- Conversion of a coordinate reflection formula to the actual weight reflection. -/
theorem weightOfLabels_reflection (v c alpha : Fin n → ℤ) (a : ι)
    (hc : corootElement P a = ∑ i : Fin n, c i • corootBasis P b (e i))
    (ha : indexedWeightCoordinates P b e (rootWeight P a) = alpha) :
    weightReflection P a (weightOfLabels P b e v) =
      weightOfLabels P b e (v - (∑ i, v i * c i) • alpha) := by
  apply (indexedWeightCoordinates P b e).injective
  rw [weightReflection_apply, map_sub, map_smul, ha,
    weightOfLabels_coroot_evaluation P b e v c a hc]
  simp [weightOfLabels]

end Atlas.Chevalley.Integral.Minuscule
