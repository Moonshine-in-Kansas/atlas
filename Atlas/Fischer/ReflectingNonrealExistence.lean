import Atlas.Fischer.OctadicNonrealPairing
import Atlas.Fischer.WittDistributions

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Each actual octad has a disjoint actual octad; this uses the verified
intersection distribution, not a chosen coordinate certificate. -/
theorem octad_exists_disjoint (O : Octad) : ∃ F : Octad, Disjoint O.val F.val := by
  classical
  have hc := (octad_intersection_distribution O.val O.property).1
  unfold octadIntersectionCount at hc
  have hn : (octads.filter (fun B => ∅ ⊆ B ∧ (B ∩ O.val).card = 0)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨F,hF⟩ := hn
  rcases Finset.mem_filter.mp hF with ⟨hFo,hFi⟩
  refine ⟨⟨F,hFo⟩, ?_⟩
  exact (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hFi.2)).symm

/-- Actual octadic displayed roots, and hence intrinsic reflecting roots,
realize a nonreal pairing. The base octad can be prescribed arbitrarily. -/
theorem reflectingRoots_exist_nonreal (O : Octad) :
    ∃ r s : Coordinates, IsReflectingRoot r ∧ IsReflectingRoot s ∧
      star (hermitian r s) ≠ hermitian r s := by
  obtain ⟨F,hF⟩ := octad_exists_disjoint O
  obtain ⟨χ,ψ,h⟩ := octadicRoot_disjoint_exists_nonreal O F hF
    (chosenOctadCalibration O) (chosenOctadCalibration F)
  exact ⟨_,_,octadicRoot_isReflectingRoot _ _,octadicRoot_isReflectingRoot _ _,h⟩

end Atlas.Fischer
