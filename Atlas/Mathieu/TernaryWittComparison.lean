import Atlas.Codes.TernaryBinaryOctadLift
import Atlas.Mathieu.TernaryWittCoordinates

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Codes

/-- The marked trace of the actual octad lift is exactly the ternary hexad support. -/
theorem ternaryWitt_trace (u : TernaryWord) (hu : u ∈ ternaryGolay)
    (hw : ternaryWeight u = 6) :
    (ternarySupport u).map ternaryWittCoordinates.toEmbedding =
      mathieu12OctadTrace ternaryComparisonDodecad (support (ternaryBinaryOctadWord u)) := by
  classical
  ext x
  obtain ⟨i,rfl⟩ := ternaryWittCoordinates.surjective x
  have hi := (ternaryBinaryOctadLift_spec u hu hw).2 i
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply, ternarySupport,
    mathieu12OctadTrace, support, Finset.mem_filter, Finset.mem_univ, true_and,
    ternaryWittCoordinates_val, hi]
  by_cases h : u i = 0 <;> simp [h]

theorem ternaryWitt_hexad_forward (B : Finset (Fin 12)) (hB : B ∈ ternaryHexads) :
    B.map ternaryWittCoordinates.toEmbedding ∈ mathieu12Blocks ternaryComparisonDodecad := by
  classical
  obtain ⟨u, hw, rfl⟩ := hB
  let O := support (ternaryBinaryOctadWord u.val)
  have hO : O ∈ octads := (octads_mem _).mpr
    ⟨⟨ternaryBinaryOctadWord u.val, ternaryBinaryOctadWord_mem _⟩,
      (ternaryBinaryOctadLift_spec u.val u.prop hw).1, rfl⟩
  have ht := ternaryWitt_trace u.val u.prop hw
  have hc : (ternaryComparisonDodecad.val ∩ O).card = 6 := by
    rw [← mathieu12OctadTrace_card ternaryComparisonDodecad O, ← ht, Finset.card_map, ternarySupport_card, hw]
  exact (mathieu12Blocks_mem _ _).mpr ⟨O, hO, hc, ht.symm⟩

/-- Actual isomorphism with the previously verified binary-Golay dodecad Witt design. -/
theorem ternaryWitt_hexads_iff (B : Finset (Fin 12)) :
    B ∈ ternaryHexads ↔
      B.map ternaryWittCoordinates.toEmbedding ∈ mathieu12Blocks ternaryComparisonDodecad := by
  classical
  constructor
  · exact ternaryWitt_hexad_forward B
  · intro hB
    have hb : B.card = 6 := by
      simpa only [Finset.card_map] using mathieu12Blocks_size _ _ hB
    obtain ⟨S,hSB,hS⟩ := Finset.exists_subset_card_eq (s := B) (n := 5) (by omega)
    obtain ⟨C,⟨hC,hSC⟩,_⟩ := ternaryHexads_steiner S hS
    obtain ⟨X,_,hx⟩ := mathieu12_steiner ternaryComparisonDodecad
      (S.map ternaryWittCoordinates.toEmbedding) (by simpa using hS)
    have he : B.map ternaryWittCoordinates.toEmbedding = C.map ternaryWittCoordinates.toEmbedding :=
      (hx _ ⟨hB, Finset.map_subset_map.mpr hSB⟩).trans
        (hx _ ⟨ternaryWitt_hexad_forward C hC, Finset.map_subset_map.mpr hSC⟩).symm
    have hBC : B = C := Finset.map_injective _ he
    exact hBC ▸ hC

end Atlas.Codes
