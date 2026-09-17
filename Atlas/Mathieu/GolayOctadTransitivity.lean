import Atlas.Mathieu.Mathieu24NotSixTransitive

noncomputable section
namespace Atlas.Codes
open Finset

theorem mathieu24_five_set_transitive (S T : Finset Omega) (hS : S.card = 5) (hT : T.card = 5) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val S = T := by
  classical
  obtain ⟨g,hg⟩ := mathieu24_five_transitive_explicit
    (finiteSetEmbedding S hS) (finiteSetEmbedding T hT)
  refine ⟨g,?_⟩
  rw [← finiteSetEmbedding_image S hS,← finiteSetEmbedding_image T hT]
  change (univ.image (finiteSetEmbedding S hS)).image g.val = _
  rw [image_image]
  exact image_congr (fun i _ => hg i)

theorem mathieu24_octad_transitive (O P : Finset Omega) (hO : O ∈ octads) (hP : P ∈ octads) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val O = P := by
  classical
  obtain ⟨S,hSO,hS⟩ := exists_subset_card_eq (s := O) (n := 5) (by rw [octad_size O hO]; decide)
  obtain ⟨T,hTP,hT⟩ := exists_subset_card_eq (s := P) (n := 5) (by rw [octad_size P hP]; decide)
  obtain ⟨g,hg⟩ := mathieu24_five_set_transitive S T hS hT
  refine ⟨g,octad_unique_on_five T _ P hT
    ((codePreserving_octadPreserving g.val g.prop O).mp hO) hP ?_ hTP⟩
  rw [← hg]
  exact image_subset_image hSO

end Atlas.Codes
