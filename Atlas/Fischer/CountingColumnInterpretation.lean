import Atlas.Fischer.CountingDiamondColumns
import Atlas.Fischer.OctadContractionWeight

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem countingColumnDelta_actual (D E : Octad) (h : OctadPairAdmissible D E) :
    countingColumnDelta (D.val ∩ E.val).card=some (octadDelta D E) := by
  rcases h with h | h <;> simp [countingColumnDelta,octadDelta,h]

theorem countingSourceAA_triple_inter_card (d e : CountingSourceTypeA) (G : Finset Omega) :
    (((countingSourceOctadEquiv (.inl d)).val ∩ (countingSourceOctadEquiv (.inl e)).val) ∩ G).card=
      ∑ i ∈ d.val ∩ e.val, countingColumnProfile G i := by
  rw [Finset.inter_assoc,countingSourceA_inter_card]
  have hi (i : Fin 6) : countingColumnProfile ((countingSourceOctadEquiv (.inl e)).val ∩ G) i=
      if i ∈ e.val then countingColumnProfile G i else 0 := by
    simp only [countingColumnProfile,countingPointColumn_inter,countingPointColumn_source,
      countingSourceColumn]
    by_cases he : i ∈ e.val <;> simp [he]
  simp_rw [hi]
  rw [← Finset.sum_filter]
  congr 1

/-- Literal column-count-rule equals the signed integer attached to the actual
five-triangle configuration; no Parker sign or orbit count is assumed. -/
theorem countingColumnWeight_actual (D E F G H J GP HP JP : Octad)
    (d e f : CountingSourceTypeA)
    (hd : countingSourceOctadEquiv (.inl d)=D)
    (he : countingSourceOctadEquiv (.inl e)=E)
    (hf : countingSourceOctadEquiv (.inl f)=F)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine)
    (hGH : octadWord G + octadWord H + octadWord J ∈ allOneCodeLine)
    (hDG : octadWord D + octadWord G + octadWord GP ∈ allOneCodeLine)
    (hEH : octadWord E + octadWord H + octadWord HP ∈ allOneCodeLine)
    (hFJ : octadWord F + octadWord J + octadWord JP ∈ allOneCodeLine) :
    countingColumnWeight (octadDelta D E) d.val e.val f.val
      (countingColumnProfile G.val) (countingColumnProfile H.val)
      (countingColumnJointProfile G.val H.val)=
        some (octadContractionIntegerWeight D E F G H J GP HP) := by
  have aGH := octadPairAdmissible_of_line G H J hGH
  have aDG := octadPairAdmissible_of_line D G GP hDG
  have aEH := octadPairAdmissible_of_line E H HP hEH
  have aFJ := octadPairAdmissible_of_line F J JP hFJ
  have hdg := countingSourceA_inter_card d G.val
  rw [hd] at hdg
  have heh := countingSourceA_inter_card e H.val
  rw [he] at heh
  have hfj := countingSourceA_inter_card f J.val
  rw [hf] at hfj
  have heg := countingSourceA_inter_card e G.val
  rw [he] at heg
  have hdeh := countingSourceAA_triple_inter_card d e H.val
  rw [hd,he] at hdeh
  have hdgh := countingSourceA_triple_inter_card d G.val H.val
  rw [hd] at hdgh
  have hj : countingDiamondColumns (octadDelta G H) (countingColumnProfile G.val)
      (countingColumnProfile H.val) (countingColumnJointProfile G.val H.val)=countingColumnProfile J.val := by
    rw [← countingColumnProfile_diamond G H aGH,octadDiamond_eq_of_line G H J aGH hGH]
  have hp := congrArg (fun z : Bit => z.val)
    (octad_contraction_delta_parity D E F G H J GP HP JP hDE hGH hDG hEH hFJ)
  simp only [ZMod.val_natCast] at hp
  have hb := octadDelta_le_one GP HP
  have hd4 : (octadDelta D E+octadDelta G H+octadDelta D G+
      octadDelta E H+octadDelta F J)%2=octadDelta GP HP := by omega
  simp only [countingColumnWeight,countingColumnJointProfile_sum,← hdg,← heh,
    countingColumnDelta_actual G H aGH,countingColumnDelta_actual D G aDG,
    countingColumnDelta_actual E H aEH,Option.bind,bind,pure,hj,← hfj,
    countingColumnDelta_actual F J aFJ,hd4,← heg,← hdeh,← hdgh,
    octadContractionIntegerWeight]

end Atlas.Fischer
