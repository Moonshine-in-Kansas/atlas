import Atlas.Fischer.DuadOctadDecomposition
import Atlas.Fischer.DuadWeightCoordinates

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadShortened_weight_sixteen_eq (O : Octad) (b : octadShortenedCode O)
    (hb : hammingNorm b.val.val=16) : b=octadShortenedOne O := by
  have hw := octadShortened_complement_weights O b
  have hz : b+octadShortenedOne O=0 := by
    apply Subtype.ext
    apply Subtype.ext
    apply hammingNorm_eq_zero.mp
    omega
  have h := congrArg (fun c : octadShortenedCode O => c+octadShortenedOne O) hz
  have hx : octadShortenedOne O+octadShortenedOne O=0 :=
    Subtype.ext (parkerGolay_add_self _)
  simpa only [add_assoc,hx,add_zero,zero_add] using h

theorem duadPair_complement_sum_weight (F G : Octad) (hFG : (F.val ∩ G.val).card=2) :
    hammingNorm (octadComplementWord F+octadComplementWord G).val=12 := by
  have he : octadComplementWord F+octadComplementWord G=octadWord F+octadWord G := by
    unfold octadComplementWord
    calc
      _ = (octadWord F+octadWord G)+(golayOne+golayOne) := by abel
      _ = _ := by rw [parkerGolay_add_self,add_zero]
  rw [he]
  have hw := binary_weight_add (octadWord F).val (octadWord G).val
  rw [octadWord_weight,octadWord_weight,overlap_inter,octadWord_support,octadWord_support,hFG] at hw
  change hammingNorm ((octadWord F).val+(octadWord G).val)=12
  omega

/-- A weight16 component plus a weight8 component cannot produce a weight8
coordinate: that would force the latter octad to avoid both marked octads. -/
theorem duadPair_mixed_weight_not_eight (F G : Octad)
    (hFG : (F.val ∩ G.val).card=2) (b : octadShortenedCode G)
    (hb : hammingNorm b.val.val=8) :
    hammingNorm (octadComplementWord F+b.val).val ≠ 8 := by
  intro h8
  have he : octadComplementWord F+b.val=(octadWord F+b.val)+golayOne := by
    unfold octadComplementWord
    abel
  rw [he] at h8
  have hw := complement_weight (octadWord F+b.val).val
  change hammingNorm ((octadWord F+b.val)+golayOne).val+
    hammingNorm (octadWord F+b.val).val=24 at hw
  rw [h8] at hw
  have h16 : hammingNorm (octadWord F+b.val).val=16 := by omega
  have ha := binary_weight_add (octadWord F).val b.val.val
  have ho : overlap (octadWord F).val b.val.val=0 := by
    change hammingNorm (octadWord F+b.val).val+2*overlap (octadWord F).val b.val.val=
      hammingNorm (octadWord F).val+hammingNorm b.val.val at ha
    rw [h16,octadWord_weight,hb] at ha
    omega
  have hF : b.val ∈ octadShortenedCode F := by
    change b.val ∈ duadShortenedCode F.val
    rw [mem_duadShortenedCode_support,Finset.disjoint_iff_inter_eq_empty]
    rw [overlap_inter,octadWord_support] at ho
    exact Finset.card_eq_zero.mp ho
  have hz := octadShortenedCode_intersection_zero F G hFG b.val hF b.property
  rw [hz] at hb
  simpa [hammingNorm] using hb

end Atlas.Fischer
