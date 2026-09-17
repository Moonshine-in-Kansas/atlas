import Atlas.Mathieu.DodecadComplement
import Atlas.Mathieu.OctadPairCounts

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octads_avoiding_point_card (a : Omega) :
    (octads.filter (fun O => a ∉ O)).card = 506 := by
  have h := Finset.card_filter_add_card_filter_not (s := octads) (fun O => a ∈ O)
  rw [octads_through_point_card,octads_card] at h
  omega

/-- Complementation pairs the dodecads through a coordinate with those avoiding it. -/
theorem dodecads_through_avoiding_card (a : Omega) :
    (dodecads.filter (fun D => a ∈ D)).card =
      (dodecads.filter (fun D => a ∉ D)).card := by
  apply Finset.card_bij (fun D _ => Dᶜ)
  · intro D hD
    obtain ⟨hD,ha⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr ⟨dodecad_complement D hD,by simpa⟩
  · intro D hD E hE he
    exact compl_injective he
  · intro D hD
    obtain ⟨hD,ha⟩ := Finset.mem_filter.mp hD
    refine ⟨Dᶜ,Finset.mem_filter.mpr ⟨dodecad_complement D hD,?_⟩,compl_compl D⟩
    simpa using ha

theorem dodecads_through_point_card (a : Omega) :
    (dodecads.filter (fun D => a ∈ D)).card = 1288 := by
  have h := Finset.card_filter_add_card_filter_not (s := dodecads) (fun D => a ∈ D)
  have he := dodecads_through_avoiding_card a
  rw [dodecads_card] at h
  omega

theorem dodecads_avoiding_point_card (a : Omega) :
    (dodecads.filter (fun D => a ∉ D)).card = 1288 := by
  rw [← dodecads_through_avoiding_card,dodecads_through_point_card]

end Atlas.Codes
