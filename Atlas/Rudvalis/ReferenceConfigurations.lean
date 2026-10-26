import Atlas.Rudvalis.IntrinsicConfigurations
import Atlas.Rudvalis.SelectedCoordinateRows

namespace Atlas.Rudvalis

noncomputable def referenceCouple : Set MinimalCross := {localReferenceCross,referenceSecondCross}

theorem coordinateFrame_isFrame : IsFrame coordinateFrame := by
  refine ⟨?_,?_⟩
  · change Nat.card coordinateFrame=28
    exact coordinateFrame_card
  · intro x hx y hy hxy
    exact (coordinateFrame_orthogonal_iff x y hx hy).mpr hxy

theorem referenceCouple_isCouple : IsCouple referenceCouple := by
  refine ⟨?_,?_⟩
  · exact Set.ncard_pair reference_crosses_ne
  · intro a ha b hb hab
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · exact (hab rfl).elim
    · exact reference_crosses_orthogonal
    · exact (crossOrthogonal_symm _ _).mp reference_crosses_orthogonal
    · exact (hab rfl).elim

theorem referenceCoordinateDozen_pairwise : referenceCoordinateDozen.Pairwise CrossOrthogonal := by
  intro x hx y hy hxy
  exact coordinateFrame_isFrame.2 (referenceCoordinateDozen_subset hx)
    (referenceCoordinateDozen_subset hy) hxy

theorem referenceCouple_subset_dozen : referenceCouple⊆referenceCoordinateDozen := by
  rintro c (rfl|rfl)
  · exact referenceCross_mem_dozen
  · exact referenceSecondCross_mem_dozen

theorem referenceDozenRows_marking (r : Fin 7) : rowLabel r∈referenceDozenRows ↔ r=0 ∨ r=4 ∨ r=5 := by
  change dot (binaryLabel 1) (rowLabel r).val=0 ↔ _
  decide +kernel +revert

end Atlas.Rudvalis
