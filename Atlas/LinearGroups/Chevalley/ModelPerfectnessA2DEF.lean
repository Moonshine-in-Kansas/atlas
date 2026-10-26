import Atlas.LinearGroups.Chevalley.ModelPerfectnessA2
import Atlas.LinearGroups.Chevalley.RootData.SingleEdgeNeighboursDEF

/-! Actual D/E/F model applications of the single-edge commutator argument.
These statements have no field-cardinality or characteristic restriction. -/

noncomputable section
namespace Atlas.Chevalley
open Group

theorem model_D_isPerfect (r : ℕ) (hr : 4 ≤ r)
    (R : Type*) [CommRing R] : IsPerfect (Model (.D r hr) R) :=
  model_isPerfect_of_a2_neighbours (.D r hr) R (D_model_single_edge_neighbours r hr)

theorem model_E6_isPerfect (R : Type*) [CommRing R] :
    IsPerfect (Model .E6 R) :=
  model_isPerfect_of_a2_neighbours .E6 R E6_model_single_edge_neighbours

theorem model_E7_isPerfect (R : Type*) [CommRing R] :
    IsPerfect (Model .E7 R) :=
  model_isPerfect_of_a2_neighbours .E7 R E7_model_single_edge_neighbours

theorem model_E8_isPerfect (R : Type*) [CommRing R] :
    IsPerfect (Model .E8 R) :=
  model_isPerfect_of_a2_neighbours .E8 R E8_model_single_edge_neighbours

theorem model_F4_isPerfect (R : Type*) [CommRing R] :
    IsPerfect (Model .F4 R) :=
  model_isPerfect_of_a2_neighbours .F4 R F4_model_single_edge_neighbours

end Atlas.Chevalley
