import Atlas.Fischer.WittParameters
import Atlas.Combinatorics.SubblockIncidenceCount

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Combinatorics
open scoped BigOperators

/-- Marked outside-set incidence moments, obtained from the actual Witt system. -/
theorem octad_intersection_moment (O T : Finset Omega) (k l : ℕ)
    (hOT : Disjoint O T)
    (hl : ∀ U : Finset Omega, U.card = T.card + k → octadReplication U = l) :
    (∑ B ∈ octads.filter (fun B => T ⊆ B), (B ∩ O).card.choose k) =
      O.card.choose k * l := by
  classical
  apply subblock_incidence_count
  intro U hU
  obtain ⟨hUO,hUk⟩ := Finset.mem_powersetCard.mp hU
  have hTU : Disjoint T U := hOT.symm.mono_right hUO
  have he : (octads.filter (fun B => T ⊆ B)).filter (fun B => U ⊆ B) =
      octads.filter (fun B => T ∪ U ⊆ B) := by
    ext B
    simp only [Finset.mem_filter,Finset.union_subset_iff]
    tauto
  rw [he]
  exact hl (T ∪ U) (by rw [Finset.card_union_of_disjoint hTU,hUk])

end Atlas.Fischer
