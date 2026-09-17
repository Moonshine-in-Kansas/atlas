import Atlas.Fischer.CountingSourceSignedMoments
import Atlas.Fischer.CountingPairWeightInterpretation
import Atlas.Fischer.CountingCanonicalTriangles
import Atlas.Fischer.QuinticOctadSignedSum

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Reindex both actual free Golay octads through the verified source equivalence. -/
theorem octadContractionSignedSum_source (D E F : Octad) (d e f : CountingSourceTypeA)
    (hd : countingSourceOctadEquiv (.inl d)=D)
    (he : countingSourceOctadEquiv (.inl e)=E)
    (hf : countingSourceOctadEquiv (.inl f)=F)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    octadContractionSignedSum D E F = ∑ t : CountingSourceParameters,
      ∑ u : CountingSourceParameters,
        (countingSourceWeight (octadDelta D E) d.val e.val f.val t u).getD 0 := by
  unfold octadContractionSignedSum
  rw [← Equiv.sum_comp countingSourceOctadEquiv]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Equiv.sum_comp countingSourceOctadEquiv]
  apply Finset.sum_congr rfl
  intro u _
  exact (countingSourcePairWeight_actual D E F d e f hd he hf hDE t u).symm

theorem countingCanonicalSextet_triangle_line :
    octadWord countingCanonicalD + octadWord countingCanonicalSextetE +
      octadWord countingCanonicalSextetF ∈ allOneCodeLine := by
  rw [countingCanonicalSextet_word,parkerGolay_add_self]
  exact allOneCodeLine.zero_mem

theorem countingCanonicalTrio_triangle_line :
    octadWord countingCanonicalD + octadWord countingCanonicalTrioE +
      octadWord countingCanonicalTrioF ∈ allOneCodeLine := by
  rw [countingCanonicalTrio_word,← add_assoc,parkerGolay_add_self,zero_add]
  exact (mem_allOneCodeLine _).mpr (Or.inr rfl)

/-- The actual canonical sextet double-octad signed contraction is13634. -/
theorem countingCanonicalSextet_signed_sum :
    octadContractionSignedSum countingCanonicalD countingCanonicalSextetE countingCanonicalSextetF=13634 := by
  have hi : (countingCanonicalD.val ∩ countingCanonicalSextetE.val).card=4 := by
    simpa only [signedOctadIntersection,signedOctadSupport_canonical] using
      octadWord_sum_weight _ _ _ countingCanonicalSextet_word
  have hd : octadDelta countingCanonicalD countingCanonicalSextetE=0 := by
    simp [octadDelta,hi]
  rw [octadContractionSignedSum_source countingCanonicalD countingCanonicalSextetE countingCanonicalSextetF
    ⟨{0,1},by decide⟩ ⟨{0,2},by decide⟩ ⟨{1,2},by decide⟩
    rfl rfl rfl countingCanonicalSextet_triangle_line,hd]
  exact countingSourceSignedSum false

/-- The actual canonical trio double-octad signed contraction is13738. -/
theorem countingCanonicalTrio_signed_sum :
    octadContractionSignedSum countingCanonicalD countingCanonicalTrioE countingCanonicalTrioF=13738 := by
  have hi : (countingCanonicalD.val ∩ countingCanonicalTrioE.val).card=0 := by
    simpa only [signedOctadIntersection,signedOctadSupport_canonical] using
      octadWord_complementary_sum_weight _ _ _ countingCanonicalTrio_word
  have hd : octadDelta countingCanonicalD countingCanonicalTrioE=1 := by
    simp [octadDelta,hi]
  rw [octadContractionSignedSum_source countingCanonicalD countingCanonicalTrioE countingCanonicalTrioF
    ⟨{0,1},by decide⟩ ⟨{2,3},by decide⟩ ⟨{4,5},by decide⟩
    rfl rfl rfl countingCanonicalTrio_triangle_line,hd]
  exact countingSourceSignedSum true

end Atlas.Fischer
