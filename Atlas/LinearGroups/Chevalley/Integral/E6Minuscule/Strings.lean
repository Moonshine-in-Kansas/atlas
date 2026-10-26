import Atlas.LinearGroups.Chevalley.Integral.MinusculeOrbitRepresentation
import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Orbit

/-! Actual E6 weight-orbit strings, using the proved orbit and all-root grades. -/
noncomputable section
namespace Atlas.Chevalley.E6Minuscule
open Integral.Minuscule
theorem weights_closed (r : E6Data.Root) (μ : Weight) (hμ : μ ∈ weights) :
    weightReflection E6Data.pairing r μ ∈ weights := by
  obtain ⟨a, rfl⟩ := (mem_weights μ).mp hμ
  obtain ⟨c, hc⟩ := root_reflection_closed r a
  exact (mem_weights _).mpr ⟨c, hc.symm⟩

def actualStrings : Strings E6Data.Root (WeightOrbit E6Data.pairing weights) :=
  stringsOfWeightOrbit E6Data.pairing weights weights_closed (by
    intro μ hμ r
    obtain ⟨a, rfl⟩ := (mem_weights μ).mp hμ
    exact all_root_grades a r)
end Atlas.Chevalley.E6Minuscule

