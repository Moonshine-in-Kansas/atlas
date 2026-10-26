import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramWeights

/-! The diagram exchanges the actual inherited 27-weight orbit with its
negative. The explicit index correspondence is checked on the existing table;
it does not identify groups from their orders or dimensions. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open E6Data Integral.Minuscule

def dualWeightIndex : Equiv.Perm (Fin 27) where
  toFun := ![26,25,24,23,22,21,19,20,17,18,15,16,12,13,14,10,11,8,9,6,7,5,4,3,2,1,0]
  invFun := ![26,25,24,23,22,21,19,20,17,18,15,16,12,13,14,10,11,8,9,6,7,5,4,3,2,1,0]
  left_inv := by decide
  right_inv := by decide

theorem dualWeightIndex_involutive : Function.Involutive dualWeightIndex := by
  intro i
  fin_cases i <;> rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem coordinateDiagram_minuscule (a : Fin 27) :
    coordinateDiagram (E6MinusculeTable.coordinates a) =
      -E6MinusculeTable.coordinates (dualWeightIndex a) := by
  funext i
  revert a i
  decide

theorem weightDiagram_minuscule (a : Fin 27) :
    weightDiagram (E6Minuscule.weight a) = -E6Minuscule.weight (dualWeightIndex a) := by
  apply (indexedWeightCoordinates pairing base baseIndexEquiv).injective
  rw [weightDiagram_coordinates, map_neg]
  simpa only [E6Minuscule.weight, weightOfLabels, LinearEquiv.apply_symm_apply] using
    coordinateDiagram_minuscule a

theorem weightDiagram_mem_negative_orbit (μ : WeightLattice pairing)
    (hμ : μ ∈ E6Minuscule.weights) :
    ∃ ν ∈ E6Minuscule.weights, weightDiagram μ = -ν := by
  obtain ⟨a, rfl⟩ := (E6Minuscule.mem_weights μ).mp hμ
  exact ⟨E6Minuscule.weight (dualWeightIndex a),
    (E6Minuscule.mem_weights _).mpr ⟨dualWeightIndex a, rfl⟩, weightDiagram_minuscule a⟩

end Atlas.Chevalley.TwistedE6
