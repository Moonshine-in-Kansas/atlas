import Atlas.Fischer.DuadDodecadObstruction
import Atlas.Fischer.OctadRestrictionCounts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Both summands are the actual retained shortened octad subcodes. -/
theorem duadOctadSubcodes_disjoint (F G : Octad) (hFG : (F.val ∩ G.val).card=2) :
    Disjoint (octadShortenedCode F) (octadShortenedCode G) := by
  rw [Submodule.disjoint_def]
  intro c hF hG
  exact octadShortenedCode_intersection_zero F G hFG c hF hG

theorem duadShortenedCode_eq_sup (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p) :
    duadShortenedCode p=octadShortenedCode F ⊔ octadShortenedCode G := by
  have hF : p ⊆ F.val := hFG ▸ Finset.inter_subset_left
  have hG : p ⊆ G.val := hFG ▸ Finset.inter_subset_right
  have hle := sup_le (octadShortenedCode_le_duad p F hF) (octadShortenedCode_le_duad p G hG)
  have hi := duadOctadSubcodes_disjoint F G (hFG ▸ hp)
  have hd := (octadShortenedCode F).finrank_sup_add_finrank_inf_eq (octadShortenedCode G)
  rw [hi.eq_bot,finrank_bot,octadShortenedCode_finrank,octadShortenedCode_finrank] at hd
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [duadShortenedCode_finrank p hp]
  omega

/-- Existence uses the77 octads through the duad and then the16 exact
intersection-duad octads relative to any chosen first octad. -/
theorem duad_octad_pair_exists (p : Finset Omega) (hp : p.card=2) :
    ∃ F G : Octad, F.val ∩ G.val=p := by
  classical
  have hc := octadReplication_two p hp
  have hpos : 0 < (octads.filter (fun F => p ⊆ F)).card := by
    change 0 < octadReplication p
    rw [hc]
    decide
  obtain ⟨F,hF⟩ := Finset.card_pos.mp hpos
  obtain ⟨hFO,hpF⟩ := Finset.mem_filter.mp hF
  have hg := octadRestrictionCount_duad F p hFO hpF hp
  have hposG : 0 < (octads.filter (fun G => G ∩ F=p)).card := by
    change 0 < octadRestrictionCount F p
    rw [hg]
    decide
  obtain ⟨G,hG⟩ := Finset.card_pos.mp hposG
  obtain ⟨hGO,hGF⟩ := Finset.mem_filter.mp hG
  exact ⟨⟨F,hFO⟩,⟨G,hGO⟩,(Finset.inter_comm F G).trans hGF⟩

/-- One explicit choice is retained for each marked duad; no independence of
this choice is asserted at the construction stage. -/
def duadChosenOctadPair (p : Finset Omega) (hp : p.card=2) : Octad × Octad :=
  let h := duad_octad_pair_exists p hp
  (Classical.choose h,Classical.choose (Classical.choose_spec h))

theorem duadChosenOctadPair_intersection (p : Finset Omega) (hp : p.card=2) :
    (duadChosenOctadPair p hp).1.val ∩ (duadChosenOctadPair p hp).2.val=p :=
  Classical.choose_spec (Classical.choose_spec (duad_octad_pair_exists p hp))

/-- No octad can avoid the union of an octad pair intersecting in a duad. -/
theorem octad_not_disjoint_duad_pair (F G O : Octad)
    (hFG : (F.val ∩ G.val).card=2) : ¬Disjoint O.val (F.val ∪ G.val) := by
  classical
  intro hO
  have hcF : octadWord O ∈ octadShortenedCode F := by
    rw [mem_octadShortenedCode]
    intro i hi
    have ho : i ∉ O.val := fun h => Finset.disjoint_left.mp hO h (Finset.mem_union_left _ hi)
    simp [octadWord_apply,ho]
  have hcG : octadWord O ∈ octadShortenedCode G := by
    rw [mem_octadShortenedCode]
    intro i hi
    have ho : i ∉ O.val := fun h => Finset.disjoint_left.mp hO h (Finset.mem_union_right _ hi)
    simp [octadWord_apply,ho]
  have hz := octadShortenedCode_intersection_zero F G hFG (octadWord O) hcF hcG
  have hw := octadWord_weight O
  rw [hz] at hw
  simpa [hammingNorm] using hw

end Atlas.Fischer
