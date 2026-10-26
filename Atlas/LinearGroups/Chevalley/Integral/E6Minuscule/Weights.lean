import Atlas.LinearGroups.Chevalley.Integral.ExceptionalCorootCoordinates
import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable

/-! Actual E6 weights defined by their fundamental-weight coordinates. -/
noncomputable section
namespace Atlas.Chevalley.E6Minuscule
open Integral.Minuscule E6Data
open scoped BigOperators
local notation "P" => E6Data.pairing
local notation "b" => E6Data.base
local notation "e" => E6Data.baseIndexEquiv
local notation "T" => E6MinusculeTable.Weight
abbrev Weight := WeightLattice P

def weight (a : T) : Weight := weightOfLabels P b e (E6MinusculeTable.coordinates a)
def selectedWeight : Weight := fundamentalWeights P b (e E6MinusculeTable.selectedNode)

theorem weight_injective : Function.Injective weight :=
  (weightOfLabels P b e).injective.comp E6MinusculeTable.coordinates_injective

def weights : Finset Weight := Finset.univ.map ⟨weight, weight_injective⟩

@[simp] theorem weights_card : weights.card = 27 := by simp [weights]
@[simp] theorem mem_weights (μ : Weight) : μ ∈ weights ↔ ∃ a : T, weight a = μ := by
  simp [weights]
@[simp] theorem weight_zero : weight 0 = selectedWeight := by
  rw [weight, E6MinusculeTable.initial_coordinates, weightOfLabels_single]
  rfl

theorem all_root_grades (a : T) (r : E6Data.Root) :
    weight a (corootElement P r) = -1 ∨ weight a (corootElement P r) = 0 ∨
      weight a (corootElement P r) = 1 := by
  apply E6Data.weight_labels_minuscule_of_representatives
  intro s
  exact E6MinusculeTable.all_root_grades a s


end Atlas.Chevalley.E6Minuscule
