import Atlas.LinearGroups.Chevalley.Integral.E7Minuscule.Weights
/-! Actual E7 minuscule weight lattice: Orbit. -/
set_option maxRecDepth 32768
noncomputable section
namespace Atlas.Chevalley.E7Minuscule
open Integral.Minuscule E7Data
open scoped BigOperators
local notation "P" => E7Data.pairing
local notation "b" => E7Data.base
local notation "e" => E7Data.baseIndexEquiv
local notation "T" => E7MinusculeTable.Weight
/-- Coordinates of any of the actual 126 roots, with no representative restriction. -/
theorem root_coordinates (r : E7Data.Root) (j : Fin 7) :
    indexedWeightCoordinates P b e (rootWeight P r) j =
      ∑ i : Fin 7, E7Table.coordinates r i * CartanMatrix.E 7 i j := by
  have hx : (∑ i : Fin 7, E7Table.coordinates r i • (Pi.single i (1 : ℤ))) =
      E7Table.coordinates r := by ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [indexedRootWeight_coordinates]
  change E7Data.datum.form (E7Data.datum.root (E7Data.datum.simpleIndex j))
    (E7Data.datum.root r) = _
  rw [E7Data.datum.simple_coordinates]
  change E7Data.datum.form (Pi.single j 1) (E7Table.coordinates r) = _
  conv_lhs => rw [← hx, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [E7Data.datum.form_symm]
  exact Matrix.toBilin'_single _ _ _

/-- Actual reflection written in fundamental-weight coordinates. -/
theorem reflection_coordinates (r : E7Data.Root) (v : Fin 7 → ℤ) :
    indexedWeightCoordinates P b e (weightReflection P r (weightOfLabels P b e v)) =
      fun j => v j - (∑ i, v i * E7Table.coordinates r i) *
        (∑ i, E7Table.coordinates r i * CartanMatrix.E 7 i j) := by
  ext j
  simp only [weightReflection_apply, map_sub, map_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, root_coordinates]
  rw [E7Data.weight_labels_coroot_evaluation]
  simp only [indexedWeightCoordinates_apply, weightOfLabels_simple_evaluation]

/-- The finite certificate covers all 126 actual roots directly. -/
theorem root_reflection_closed (r : E7Data.Root) (a : T) :
    ∃ c : T, weightReflection P r (weight a) = weight c := by
  refine ⟨E7MinusculeTable.rootReflectionIndex r a, ?_⟩
  apply (indexedWeightCoordinates P b e).injective
  rw [weight, reflection_coordinates]
  simp only [weight, weightOfLabels, LinearEquiv.apply_symm_apply]
  exact (E7MinusculeTable.root_reflection_coordinates a r).symm

theorem simple_reflection_labels (i : Fin 7) (v : Fin 7 → ℤ) :
    weightReflection P (e i) (weightOfLabels P b e v) =
      weightOfLabels P b e (E7MinusculeTable.reflectSimple i v) := by
  apply (indexedWeightCoordinates P b e).injective
  rw [reflection_coordinates]
  simp only [weightOfLabels, LinearEquiv.apply_symm_apply]
  ext j
  have hs : E7Table.coordinates (e i) = Pi.single i 1 := by
    change E7Data.datum.root (E7Data.datum.simpleIndex i) = _
    exact E7Data.datum.simple_coordinates i
  rw [hs]
  simp [E7MinusculeTable.reflectSimple, Pi.single_apply]

/-- A word here acts by actual coroot reflections on P, not by a table action. -/
def reflectionWord : List (Fin 7) → Weight → Weight
  | [], μ => μ
  | i :: w, μ => reflectionWord w (weightReflection P (e i) μ)

theorem reflectionWord_labels (w : List (Fin 7)) (v : Fin 7 → ℤ) :
    reflectionWord w (weightOfLabels P b e v) =
      weightOfLabels P b e (E7MinusculeTable.wordAction w v) := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih =>
    simp only [reflectionWord, E7MinusculeTable.wordAction, simple_reflection_labels, ih]

/-- Explicit reachability of every actual weight from the chosen fundamental weight. -/
theorem weight_reachable (a : T) :
    reflectionWord (E7MinusculeTable.weightWord a) selectedWeight = weight a := by
  rw [show selectedWeight = weightOfLabels P b e
      (Pi.single E7MinusculeTable.selectedNode 1) from (weightOfLabels_single P b e _).symm,
    reflectionWord_labels, E7MinusculeTable.weight_word_coordinates]
  rfl

theorem reflectionWord_closed (w : List (Fin 7)) {μ : Weight} (hμ : μ ∈ weights) :
    reflectionWord w μ ∈ weights := by
  induction w generalizing μ with
  | nil => exact hμ
  | cons i w ih =>
    obtain ⟨a, rfl⟩ := (mem_weights μ).mp hμ
    obtain ⟨c, hc⟩ := root_reflection_closed (e i) a
    exact ih ((mem_weights _).mpr ⟨c, hc.symm⟩)

/-- Exactly the orbit under finite simple-reflection words; no extra points. -/
theorem mem_weights_iff_reachable (μ : Weight) :
    μ ∈ weights ↔ ∃ w : List (Fin 7), reflectionWord w selectedWeight = μ := by
  constructor
  · rintro h
    obtain ⟨a, rfl⟩ := (mem_weights μ).mp h
    exact ⟨E7MinusculeTable.weightWord a, weight_reachable a⟩
  · rintro ⟨w, rfl⟩
    exact reflectionWord_closed w ((mem_weights _).mpr ⟨0, weight_zero⟩)


end Atlas.Chevalley.E7Minuscule
