import Atlas.Sporadic.Conway2Geometry
import Atlas.Conway.Co2SignCommutators
import Atlas.Conway.Co2Connector

noncomputable section
namespace Atlas.Sporadic.Conway2
open Atlas.Conway

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := co2_noncommuting_pair

def connector : Model := co2ConnectorElement

theorem connector_sq : connector * connector = 1 := Subtype.ext co2Connector_sq

theorem connector_outside_local : connector ∉ LocalGroup := by
  intro h
  exact co2Connector_not_monomial
    ((le_of_eq (orthogonalLineStabilizer_eq_monomial ((0,0),0) ((0,0),1) (by decide))) h)

end Atlas.Sporadic.Conway2
