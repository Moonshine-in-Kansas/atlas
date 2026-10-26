import Atlas.LinearGroups.Chevalley.Integral.ExceptionalCorootCoordinates
import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable

/-! Actual E7 minuscule weight lattice: Weights. -/
noncomputable section
namespace Atlas.Chevalley.E7Minuscule
open Integral.Minuscule E7Data
open scoped BigOperators
local notation "P" => E7Data.pairing
local notation "b" => E7Data.base
local notation "e" => E7Data.baseIndexEquiv
local notation "T" => E7MinusculeTable.Weight
abbrev Weight := WeightLattice P

def weight (a : T) : Weight := weightOfLabels P b e (E7MinusculeTable.coordinates a)
def selectedWeight : Weight := fundamentalWeights P b (e E7MinusculeTable.selectedNode)

theorem weight_injective : Function.Injective weight :=
  (weightOfLabels P b e).injective.comp E7MinusculeTable.coordinates_injective

def weights : Finset Weight := Finset.univ.map ⟨weight, weight_injective⟩

@[simp] theorem weights_card : weights.card = 56 := by simp [weights]
@[simp] theorem mem_weights (μ : Weight) : μ ∈ weights ↔ ∃ a : T, weight a = μ := by
  simp [weights]
@[simp] theorem weight_zero : weight 0 = selectedWeight := by
  rw [weight, E7MinusculeTable.initial_coordinates, weightOfLabels_single]
  rfl

theorem all_root_grades (a : T) (r : E7Data.Root) :
    weight a (corootElement P r) = -1 ∨ weight a (corootElement P r) = 0 ∨
      weight a (corootElement P r) = 1 := by
  simpa only [weight, E7Data.weight_labels_coroot_evaluation,
    E7MinusculeTable.grade, E7MinusculeTable.rootCoefficients] using
      E7MinusculeTable.all_root_grades a r


end Atlas.Chevalley.E7Minuscule
