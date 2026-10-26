import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionA2
import Atlas.LinearGroups.Chevalley.ModelPerfectnessA2
import Atlas.LinearGroups.Chevalley.RootData.SingleEdgeNeighboursDEF

/-! All-ring perfectness for the actual selected-weight A, D, E and F companions.
Only their proved actual single-edge neighbours are supplied to the simultaneous
A2 argument; no characteristic, cardinality, center, or projection-kernel premise. -/

noncomputable section
namespace Atlas.Chevalley
open Group

private theorem selectedCompanion_perfect_of_base_neighbours
    (Φ : RootType) (R : Type*) [CommRing R]
    (hrows : ∀ i : (rootDatum Φ).base.support, ∃ j : (rootDatum Φ).base.support,
      j ≠ i ∧ (rootDatum Φ).base.cartanMatrix i j = -1 ∧
        (rootDatum Φ).base.cartanMatrix j i = -1) :
    IsPerfect (SelectedWeightCompanion Φ R) := by
  apply selectedWeightCompanion_isPerfect_of_a2_neighbours Φ R
  intro i
  obtain ⟨j, hne, hij, hji⟩ := hrows ((rootDatum Φ).indexEquiv i)
  obtain ⟨k, rfl⟩ := (rootDatum Φ).indexEquiv.surjective j
  exact ⟨k, fun h => hne (congrArg (rootDatum Φ).indexEquiv h), hij, hji⟩

theorem selectedWeightCompanion_A_isPerfect_of_rank_ge_two
    (r : ℕ) (hr : 2 ≤ r) (R : Type*) [CommRing R] :
    IsPerfect (SelectedWeightCompanion (.A r (by omega)) R) := by
  apply selectedCompanion_perfect_of_base_neighbours (.A r (by omega)) R
  with_unfolding_all exact A_base_a2_neighbours r hr

theorem selectedWeightCompanion_D_isPerfect_of_rank_ge_four
    (r : ℕ) (hr : 4 ≤ r) (R : Type*) [CommRing R] :
    IsPerfect (SelectedWeightCompanion (.D r hr) R) :=
  selectedWeightCompanion_isPerfect_of_a2_neighbours (.D r hr) R
    (D_model_single_edge_neighbours r hr)

theorem selectedWeightCompanion_E6_isPerfect (R : Type*) [CommRing R] :
    IsPerfect (SelectedWeightCompanion .E6 R) :=
  selectedWeightCompanion_isPerfect_of_a2_neighbours .E6 R E6_model_single_edge_neighbours

theorem selectedWeightCompanion_E7_isPerfect (R : Type*) [CommRing R] :
    IsPerfect (SelectedWeightCompanion .E7 R) :=
  selectedWeightCompanion_isPerfect_of_a2_neighbours .E7 R E7_model_single_edge_neighbours

theorem selectedWeightCompanion_E8_isPerfect (R : Type*) [CommRing R] :
    IsPerfect (SelectedWeightCompanion .E8 R) :=
  selectedWeightCompanion_isPerfect_of_a2_neighbours .E8 R E8_model_single_edge_neighbours

theorem selectedWeightCompanion_F4_isPerfect (R : Type*) [CommRing R] :
    IsPerfect (SelectedWeightCompanion .F4 R) :=
  selectedWeightCompanion_isPerfect_of_a2_neighbours .F4 R F4_model_single_edge_neighbours

end Atlas.Chevalley
