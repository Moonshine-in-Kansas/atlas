import Atlas.Fischer.CubicDisjointPairColumns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Canonical ordered overlapping pairs are reached by actual Mathieu elements. -/
theorem cubicSextetPair_canonical (D E : Octad) (h : (D.val ∩ E.val).card = 4) :
    ∃ g : Mathieu24CodeModel, g • D = countingCanonicalD ∧ g • E = countingCanonicalSextetE := by
  obtain ⟨g,i,j,k,hij,hik,hjk,hD,hE⟩ := cubicCommonNeighbor_pair_normalize D E h
  obtain ⟨s,hsD,hsE⟩ := cubicColumnSextetPair_canonical i j k hij hik hjk
  refine ⟨s*g,?_,?_⟩ <;> rw [mul_smul] <;> apply Subtype.ext
  · change permuteBlock s.val (g • D).val = _
    rw [hD,hsD]
  · change permuteBlock s.val (g • E).val = _
    rw [hE,hsE]

/-- The disjoint-pair route uses an actual common four-neighbor and the retained
sextet reconstruction, followed by an actual permutation of its six columns. -/
theorem cubicTrioPair_canonical (D E : Octad) (h : (D.val ∩ E.val).card = 0) :
    ∃ g : Mathieu24CodeModel, g • D = countingCanonicalD ∧ g • E = countingCanonicalTrioE := by
  obtain ⟨g,i,j,k,l,hij,hki,hkj,hli,hlj,hkl,hD,hE⟩ := cubicDisjointPair_column_normalize D E h
  obtain ⟨s,hsD,hsE⟩ := cubicColumnTrioPair_canonical i j k l hij hki hkj hli hlj hkl
  refine ⟨s*g,?_,?_⟩ <;> rw [mul_smul] <;> apply Subtype.ext
  · change permuteBlock s.val (g • D).val = _
    rw [hD,hsD]
  · change permuteBlock s.val (g • E).val = _
    rw [hE,hsE]

theorem cubicSextetTriangle_canonical (D E F : Octad)
    (h : octadWord F = octadWord D + octadWord E) :
    ∃ g : Mathieu24CodeModel, g • D = countingCanonicalD ∧
      g • E = countingCanonicalSextetE ∧ g • F = countingCanonicalSextetF := by
  obtain ⟨g,hD,hE⟩ := cubicSextetPair_canonical D E (by simpa only [signedOctadIntersection,signedOctadSupport_canonical] using octadWord_sum_weight F D E h)
  refine ⟨g,hD,hE,octadWord_injective ?_⟩
  rw [cubicTriangle_word_smul,h,map_add,← cubicTriangle_word_smul,
    ← cubicTriangle_word_smul,hD,hE,countingCanonicalSextet_word]

theorem cubicTrioTriangle_canonical (D E F : Octad)
    (h : octadWord F = octadWord D + octadWord E + golayOne) :
    ∃ g : Mathieu24CodeModel, g • D = countingCanonicalD ∧
      g • E = countingCanonicalTrioE ∧ g • F = countingCanonicalTrioF := by
  obtain ⟨g,hD,hE⟩ := cubicTrioPair_canonical D E (by simpa only [signedOctadIntersection,signedOctadSupport_canonical] using octadWord_complementary_sum_weight F D E h)
  refine ⟨g,hD,hE,octadWord_injective ?_⟩
  rw [cubicTriangle_word_smul,h,map_add,map_add,← cubicTriangle_word_smul,
    ← cubicTriangle_word_smul,cubicTriangle_one_fixed,hD,hE,countingCanonicalTrio_word]

end Atlas.Fischer
