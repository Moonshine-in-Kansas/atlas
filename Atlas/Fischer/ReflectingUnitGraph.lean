import Atlas.Fischer.RayKernelPhaseRigidity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Exact unit pairing, using the retained displayed representatives. -/
def reflectingUnitGraph : SimpleGraph ReflectingRootParameter where
  Adj i j := i ≠ j ∧ hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=1
  symm := ⟨fun i j h => ⟨h.1.symm,by rw [← hermitian_star,h.2,star_one]⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem reflectingUnitGraph_adj_of_pairing_one (i j : ReflectingRootParameter)
    (h : hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j)=1) :
    reflectingUnitGraph.Adj i j := by
  refine ⟨?_,h⟩
  intro he
  subst j
  rw [(reflectingRootParameter_isReflectingRoot i).1.1] at h
  norm_num at h

/-- Every representative reaches a basic root by one exact unit edge, and
any two distinct basic roots have exact unit pairing. -/
theorem reflectingUnitGraph_connected : reflectingUnitGraph.Connected := by
  constructor
  intro i j
  obtain ⟨a,ha⟩ := reflectingRootParameter_basic_neighbor i
  obtain ⟨b,hb⟩ := reflectingRootParameter_basic_neighbor j
  have hi : reflectingUnitGraph.Adj i (.inl a) := by
    apply reflectingUnitGraph_adj_of_pairing_one
    change hermitian (reflectingRootParameterVector i) (basicAxis a)=1
    rw [← hermitian_star,ha,star_one]
  have hj : reflectingUnitGraph.Adj (.inl b) j := reflectingUnitGraph_adj_of_pairing_one _ _ hb
  have hab : reflectingUnitGraph.Reachable (.inl a) (.inl b) := by
    by_cases h : a=b
    · subst b
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      apply reflectingUnitGraph_adj_of_pairing_one
      change hermitian (basicAxis a) (basicAxis b)=1
      rw [hermitian_basicAxis_basicAxis,if_neg h]
  exact hi.reachable.trans (hab.trans hj.reachable)

end Atlas.Fischer
