import Atlas.Fischer.WittParameters
import Atlas.Fischer.MathieuOctadTranslations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadReplication_avoidance_bound (T : Finset Omega) (hT : T.card ≤ 4)
    (x y : Omega) (hx : x ∉ T) (hy : y ∉ T) :
    octadReplication (insert x T) + octadReplication (insert y T) < octadReplication T := by
  have hxc : (insert x T).card = T.card+1 := Finset.card_insert_of_notMem hx
  have hyc : (insert y T).card = T.card+1 := Finset.card_insert_of_notMem hy
  interval_cases h : T.card
  · rw [octadReplication_zero T h,octadReplication_one _ (by omega),
      octadReplication_one _ (by omega)]; decide
  · rw [octadReplication_one T h,octadReplication_two _ (by omega),
      octadReplication_two _ (by omega)]; decide
  · rw [octadReplication_two T h,octadReplication_three _ (by omega),
      octadReplication_three _ (by omega)]; decide
  · rw [octadReplication_three T h,octadReplication_four _ (by omega),
      octadReplication_four _ (by omega)]; decide
  · rw [octadReplication_four T h,octadReplication_five _ (by omega),
      octadReplication_five _ (by omega)]; decide

/-- The source's positive replication differences produce an actual octad,
without assuming a transitivity or a Mathieu stabilizer theorem. -/
theorem octad_contains_avoids_two (T : Finset Omega) (hT : T.card ≤ 4)
    (x y : Omega) (hx : x ∉ T) (hy : y ∉ T) :
    ∃ O : Octad, T ⊆ O.val ∧ x ∉ O.val ∧ y ∉ O.val := by
  classical
  by_contra! hn
  let A := octads.filter (fun O => T ⊆ O)
  let B := octads.filter (fun O => insert x T ⊆ O)
  let C := octads.filter (fun O => insert y T ⊆ O)
  have hs : A ⊆ B ∪ C := by
    intro O hO
    obtain ⟨hO,hTO⟩ := Finset.mem_filter.mp hO
    by_cases hxo : x ∈ O
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hO,Finset.insert_subset_iff.mpr ⟨hxo,hTO⟩⟩)
    · have hyo : y ∈ O := hn ⟨O,hO⟩ hTO hxo
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hO,Finset.insert_subset_iff.mpr ⟨hyo,hTO⟩⟩)
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le B C)
  have hb := octadReplication_avoidance_bound T hT x y hx hy
  change octadReplication T ≤ octadReplication (insert x T)+octadReplication (insert y T) at hc
  omega

/-- Actual pointwise octad elements, viewed in the retained Mathieu group. -/
def octadPointwiseEmbedding (O : Octad) : mathieuOctadPointwise O →* Mathieu24CodeModel :=
  (mathieuOctadStabilizer O).subtype.comp (mathieuOctadPointwise O).subtype

theorem octadPointwiseEmbedding_fixes (O : Octad) (g : mathieuOctadPointwise O)
    (i : Omega) (hi : i ∈ O.val) : (octadPointwiseEmbedding O g).val i=i := by
  have he : mathieuOctadAlternatingHom O g.val=1 := g.prop
  exact congrArg (fun h : alternatingGroup (OctadInterior O) => (h.val ⟨i,hi⟩).val) he

/-- A generator can align two exterior points while fixing any chosen at most
four marked coordinates. -/
theorem octad_translation_align (T : Finset Omega) (hT : T.card ≤ 4)
    (x y : Omega) (hx : x ∉ T) (hy : y ∉ T) :
    ∃ O : Octad, ∃ g : mathieuOctadPointwise O,
      T ⊆ O.val ∧ (octadPointwiseEmbedding O g).val x=y ∧
      ∀ i ∈ T, (octadPointwiseEmbedding O g).val i=i := by
  obtain ⟨O,hTO,hxO,hyO⟩ := octad_contains_avoids_two T hT x y hx hy
  obtain ⟨g,hg,_⟩ := mathieuOctadPointwise_regular O ⟨x,hxO⟩ ⟨y,hyO⟩
  refine ⟨O,g,hTO,?_,fun i hi => octadPointwiseEmbedding_fixes O g i (hTO hi)⟩
  exact congrArg Subtype.val hg

end Atlas.Fischer
