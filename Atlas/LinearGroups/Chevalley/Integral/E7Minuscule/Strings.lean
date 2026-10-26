import Atlas.LinearGroups.Chevalley.Integral.MinusculeOrbitRepresentation
import Atlas.LinearGroups.Chevalley.Integral.E7Minuscule.Orbit

/-! Actual E7 minuscule weight lattice: Strings. -/
noncomputable section
namespace Atlas.Chevalley.E7Minuscule
open Integral.Minuscule
theorem weights_closed (r : E7Data.Root) (μ : Weight) (hμ : μ ∈ weights) :
    weightReflection E7Data.pairing r μ ∈ weights := by
  obtain ⟨a, rfl⟩ := (mem_weights μ).mp hμ
  obtain ⟨c, hc⟩ := root_reflection_closed r a
  exact (mem_weights _).mpr ⟨c, hc.symm⟩

def actualStrings : Strings E7Data.Root (WeightOrbit E7Data.pairing weights) :=
  stringsOfWeightOrbit E7Data.pairing weights weights_closed (by
    intro μ hμ r
    obtain ⟨a, rfl⟩ := (mem_weights μ).mp hμ
    exact all_root_grades a r)
end Atlas.Chevalley.E7Minuscule
