import Atlas.Fischer.OctadDuadIntersections
import Atlas.Fischer.OctadicRootCoordinates

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- A duad octad cannot be disjoint from an exterior affine hyperplane. Otherwise
complementing their union gives an actual octad meeting O in six points. -/
theorem octadDuad_shortened_overlap_ne_zero (O D : Octad)
    (hD : (D.val ∩ O.val).card=2) (b : OctadShortenedHyperplane O) :
    overlap (octadWord D).val b.val.val.val ≠ 0 := by
  intro hz
  let c : golay := octadWord D+b.val.val+golayOne
  have ha := binary_weight_add (octadWord D).val b.val.val.val
  rw [octadWord_weight,octadShortenedHyperplane_weight O b,hz] at ha
  have hc : hammingNorm c.val=8 := by
    have h := complement_weight ((octadWord D).val+b.val.val.val)
    change hammingNorm c.val+hammingNorm ((octadWord D).val+b.val.val.val)=24 at h
    omega
  have hC : support c.val ∈ octads := (octads_mem _).mpr ⟨c,hc,rfl⟩
  have hi : support c.val ∩ O.val=O.val \ D.val := by
    ext i
    by_cases ho : i ∈ O.val
    · have hb := (mem_octadShortenedCode O b.val.val).mp b.val.property i ho
      simp only [Finset.mem_inter,Finset.mem_sdiff,ho,true_and,and_true,
        support,Finset.mem_filter,Finset.mem_univ]
      change ((octadWord D).val i+b.val.val.val i+(1 : Bit) ≠ 0) ↔ i ∉ D.val
      rw [hb,add_zero,octadWord_apply]
      split_ifs <;> simp_all [show (2 : Bit)=0 from rfl]
    · simp [ho]
  have hcount : (support c.val ∩ O.val).card=6 := by
    rw [hi,Finset.card_sdiff]
    have hcard := octad_size O.val O.property
    rw [hD]
    omega
  have ht := octad_intersection_sizes _ _ hC O.property
  omega

end Atlas.Fischer
