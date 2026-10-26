import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Weights
/-! Actual E6 reflection orbit in the coroot-dual weight lattice. -/
noncomputable section
namespace Atlas.Chevalley.E6Minuscule
open Integral.Minuscule E6Data
open scoped BigOperators
local notation "P" => E6Data.pairing
local notation "b" => E6Data.base
local notation "e" => E6Data.baseIndexEquiv
local notation "T" => E6MinusculeTable.Weight
/-- Coordinates of any actual root weight, not merely positive representatives. -/
theorem root_coordinates (r : E6Data.Root) (j : Fin 6) :
    indexedWeightCoordinates P b e (rootWeight P r) j =
      ∑ i : Fin 6, r.val (E6Data.nodeEquiv.symm i) * CartanMatrix.E 6 i j := by
  have hx : (∑ i : Fin 6, r.val (E6Data.nodeEquiv.symm i) •
      (Pi.single (E6Data.nodeEquiv.symm i) (1 : ℤ))) = r.val := by
    calc
      _ = ∑ i : Fin 6, r.val i • (Pi.single i (1 : ℤ)) :=
        E6Data.nodeEquiv.symm.sum_comp (fun i => r.val i • Pi.single i (1 : ℤ))
      _ = r.val := by ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [indexedRootWeight_coordinates]
  change E6Data.polar (Pi.single (E6Data.nodeEquiv.symm j) 1) r.val = _
  conv_lhs => rw [← hx, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [E6Data.polar_symm]
  simpa [E6Data.simpleRoot] using
    E6Data.simple_cartan (E6Data.nodeEquiv.symm i) (E6Data.nodeEquiv.symm j)

/-- Actual reflection written in fundamental-weight coordinates. -/
theorem reflection_coordinates (r : E6Data.Root) (v : Fin 6 → ℤ) :
    indexedWeightCoordinates P b e (weightReflection P r (weightOfLabels P b e v)) =
      fun j => v j - (∑ i, v i * r.val (E6Data.nodeEquiv.symm i)) *
        (∑ i, r.val (E6Data.nodeEquiv.symm i) * CartanMatrix.E 6 i j) := by
  ext j
  simp only [weightReflection_apply, map_sub, map_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, root_coordinates]
  rw [E6Data.weight_labels_coroot_evaluation]
  simp only [indexedWeightCoordinates_apply, weightOfLabels_simple_evaluation]

/-- Every actual root reflection preserves the finite set: both signs of all
36 representatives are covered, so no 36-root truncation is hidden here. -/
theorem root_reflection_closed (r : E6Data.Root) (a : T) :
    ∃ c : T, weightReflection P r (weight a) = weight c := by
  obtain ⟨s, hs | hs⟩ := Atlas.Comparisons.E6Lattice.root_representative_exhaustion r.val r.property
  all_goals
    refine ⟨E6MinusculeTable.rootReflectionIndex s a, ?_⟩
    apply (indexedWeightCoordinates P b e).injective
    rw [weight, reflection_coordinates]
    simp only [weight, weightOfLabels, LinearEquiv.apply_symm_apply]
    rw [E6MinusculeTable.root_reflection_coordinates]
    ext j
    simp [E6MinusculeTable.reflectRoot, E6MinusculeTable.rootCoefficients, hs,
      Finset.sum_neg_distrib, Finset.sum_mul]

theorem simple_reflection_labels (i : Fin 6) (v : Fin 6 → ℤ) :
    weightReflection P (e i) (weightOfLabels P b e v) =
      weightOfLabels P b e (E6MinusculeTable.reflectSimple i v) := by
  apply (indexedWeightCoordinates P b e).injective
  rw [reflection_coordinates]
  simp only [weightOfLabels, LinearEquiv.apply_symm_apply]
  ext j
  simp [E6Data.baseIndexEquiv_apply, E6Data.simpleRoot,
    E6MinusculeTable.reflectSimple, Pi.single_apply]

/-- A word here acts by actual coroot reflections on P, not by a table action. -/
def reflectionWord : List (Fin 6) → Weight → Weight
  | [], μ => μ
  | i :: w, μ => reflectionWord w (weightReflection P (e i) μ)

theorem reflectionWord_labels (w : List (Fin 6)) (v : Fin 6 → ℤ) :
    reflectionWord w (weightOfLabels P b e v) =
      weightOfLabels P b e (E6MinusculeTable.wordAction w v) := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih =>
    simp only [reflectionWord, E6MinusculeTable.wordAction, simple_reflection_labels, ih]

/-- Explicit reachability of every actual weight from the chosen fundamental weight. -/
theorem weight_reachable (a : T) :
    reflectionWord (E6MinusculeTable.weightWord a) selectedWeight = weight a := by
  rw [show selectedWeight = weightOfLabels P b e
      (Pi.single E6MinusculeTable.selectedNode 1) from (weightOfLabels_single P b e _).symm,
    reflectionWord_labels, E6MinusculeTable.weight_word_coordinates]
  rfl

theorem reflectionWord_closed (w : List (Fin 6)) {μ : Weight} (hμ : μ ∈ weights) :
    reflectionWord w μ ∈ weights := by
  induction w generalizing μ with
  | nil => exact hμ
  | cons i w ih =>
    obtain ⟨a, rfl⟩ := (mem_weights μ).mp hμ
    obtain ⟨c, hc⟩ := root_reflection_closed (e i) a
    exact ih ((mem_weights _).mpr ⟨c, hc.symm⟩)

/-- Exactly the orbit under finite simple-reflection words; no extra points. -/
theorem mem_weights_iff_reachable (μ : Weight) :
    μ ∈ weights ↔ ∃ w : List (Fin 6), reflectionWord w selectedWeight = μ := by
  constructor
  · rintro h
    obtain ⟨a, rfl⟩ := (mem_weights μ).mp h
    exact ⟨E6MinusculeTable.weightWord a, weight_reachable a⟩
  · rintro ⟨w, rfl⟩
    exact reflectionWord_closed w ((mem_weights _).mpr ⟨0, weight_zero⟩)


end Atlas.Chevalley.E6Minuscule
