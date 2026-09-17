import Atlas.Fischer.CountingColumnInterpretation
import Atlas.Fischer.CountingColumnTranslation
import Atlas.Fischer.OctadContractionPairWeight

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem countingColumnDelta_invalid (D E : Octad) (h : ¬OctadPairAdmissible D E) :
    countingColumnDelta (D.val ∩ E.val).card=none := by
  simp only [OctadPairAdmissible,not_or] at h
  simp [countingColumnDelta,h.1,h.2]

/-- Total interpretation of the source column rule, including every invalid
configuration: absent optional weights agree with zero in the actual lattice sum. -/
theorem countingColumnPairWeight_actual (D E F G H : Octad)
    (d e f : CountingSourceTypeA)
    (hd : countingSourceOctadEquiv (.inl d)=D)
    (he : countingSourceOctadEquiv (.inl e)=E)
    (hf : countingSourceOctadEquiv (.inl f)=F)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    (countingColumnWeight (octadDelta D E) d.val e.val f.val
      (countingColumnProfile G.val) (countingColumnProfile H.val)
      (countingColumnJointProfile G.val H.val)).getD 0=octadContractionPairWeight D E F G H := by
  have hdg := countingSourceA_inter_card d G.val
  rw [hd] at hdg
  have heh := countingSourceA_inter_card e H.val
  rw [he] at heh
  unfold octadContractionPairWeight
  split_ifs with hGH hDG hEH hFJ
  · let J := octadDiamond G H hGH
    let GP := octadDiamond D G hDG
    let HP := octadDiamond E H hEH
    let JP := octadDiamond F J hFJ
    have hw := countingColumnWeight_actual D E F G H J GP HP JP d e f hd he hf hDE
      (octadDiamond_triangle_line G H hGH) (octadDiamond_triangle_line D G hDG)
      (octadDiamond_triangle_line E H hEH) (octadDiamond_triangle_line F J hFJ)
    rw [hw]
    rfl
  · have hfj := countingSourceA_inter_card f (octadDiamond G H hGH).val
    rw [hf] at hfj
    have hj := countingColumnProfile_diamond G H hGH
    simp only [countingColumnWeight,countingColumnJointProfile_sum,← hdg,← heh,
      countingColumnDelta_actual G H hGH,countingColumnDelta_actual D G hDG,
      countingColumnDelta_actual E H hEH,Option.bind,bind,← hj,← hfj,
      countingColumnDelta_invalid F (octadDiamond G H hGH) hFJ,Option.getD]
  · simp only [countingColumnWeight,countingColumnJointProfile_sum,← hdg,← heh,
      countingColumnDelta_actual G H hGH,countingColumnDelta_actual D G hDG,
      countingColumnDelta_invalid E H hEH,Option.bind,bind,Option.getD]
  · simp only [countingColumnWeight,countingColumnJointProfile_sum,← hdg,
      countingColumnDelta_actual G H hGH,countingColumnDelta_invalid D G hDG,
      Option.bind,bind,Option.getD]
  · simp only [countingColumnWeight,countingColumnJointProfile_sum,
      countingColumnDelta_invalid G H hGH,Option.bind,bind,Option.getD]

/-- Actual source parameters interpret the total signed two-free-octad summand. -/
theorem countingSourcePairWeight_actual (D E F : Octad) (d e f : CountingSourceTypeA)
    (hd : countingSourceOctadEquiv (.inl d)=D)
    (he : countingSourceOctadEquiv (.inl e)=E)
    (hf : countingSourceOctadEquiv (.inl f)=F)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine)
    (t u : CountingSourceParameters) :
    (countingSourceWeight (octadDelta D E) d.val e.val f.val t u).getD 0=
      octadContractionPairWeight D E F (countingSourceOctadEquiv t) (countingSourceOctadEquiv u) := by
  have hw := countingColumnPairWeight_actual D E F (countingSourceOctadEquiv t)
    (countingSourceOctadEquiv u) d e f hd he hf hDE
  have hp (v : CountingSourceParameters) : countingColumnProfile (countingSourceOctadEquiv v).val=
      fun i => (countingSourceColumn v i).card := by
    funext i
    exact congrArg Finset.card (countingPointColumn_source v i)
  have hj : countingColumnJointProfile (countingSourceOctadEquiv t).val
      (countingSourceOctadEquiv u).val=fun i => (countingSourceColumn t i ∩ countingSourceColumn u i).card := by
    funext i
    change (countingPointColumn (countingSourceOctadEquiv t).val i ∩
      countingPointColumn (countingSourceOctadEquiv u).val i).card=_
    rw [countingPointColumn_source t i,countingPointColumn_source u i]
  rw [hp t,hp u,hj] at hw
  exact hw


end Atlas.Fischer
