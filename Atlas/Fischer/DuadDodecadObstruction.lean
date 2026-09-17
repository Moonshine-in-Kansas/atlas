import Atlas.Fischer.DuadShortenedCode
import Atlas.Fischer.OctadShortenedDivisibility
import Atlas.Conway.GolayDodecadRestriction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Conway Atlas.Lattices

/-- The retained Golay support theorem excludes an octad in every actual dodecad. -/
theorem octad_not_subset_dodecad (D : golay) (hD : hammingNorm D.val=12) (O : Octad) :
    ¬O.val ⊆ support D.val := by
  intro hO
  have he : supportWord (support D.val)=D.val := binarySupportEquiv.left_inv D.val
  have hc : supportWord (support D.val) ∈ golay := by
    rw [he]
    exact D.property
  rcases golay_supported_dodecad (support D.val) hD hc (octadWord O).val
    (octadWord O).property (by simpa only [octadWord_support] using hO) with h | h
  · have hw := octadWord_weight O
    rw [h] at hw
    simpa [hammingNorm] using hw
  · have hw := congrArg hammingNorm h
    rw [octadWord_weight,he,hD] at hw
    omega

/-- Golay words supported away from both octads cannot be nonzero: adding the
weight12 symmetric difference would force forbidden weight20 or28. -/
theorem octadShortenedCode_intersection_zero (F G : Octad)
    (hFG : (F.val ∩ G.val).card=2) (c : golay)
    (hF : c ∈ octadShortenedCode F) (hG : c ∈ octadShortenedCode G) : c=0 := by
  classical
  have hsum : hammingNorm ((octadWord F + octadWord G).val)=12 := by
    have hw := binary_weight_add (octadWord F).val (octadWord G).val
    rw [octadWord_weight,octadWord_weight,overlap_inter,octadWord_support,octadWord_support,hFG] at hw
    change hammingNorm ((octadWord F).val+(octadWord G).val)=12
    omega
  have hov : overlap c.val (octadWord F + octadWord G).val=0 := by
    rw [overlap_eq_sum]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hiF : i ∈ F.val
    · have hz := (mem_octadShortenedCode F c).mp hF i hiF
      simp [hz]
    · by_cases hiG : i ∈ G.val
      · have hz := (mem_octadShortenedCode G c).mp hG i hiG
        simp [hz]
      · simp [octadWord_apply,hiF,hiG]
  have hw := binary_weight_add c.val (octadWord F + octadWord G).val
  rw [hov,hsum] at hw
  have hc := octadShortened_weights F ⟨c,hF⟩
  have ht := golay_weights (c+(octadWord F+octadWord G))
  have hz : hammingNorm c.val=0 := by
    change hammingNorm (c.val+(octadWord F+octadWord G).val)=0 ∨
      hammingNorm (c.val+(octadWord F+octadWord G).val)=8 ∨
      hammingNorm (c.val+(octadWord F+octadWord G).val)=12 ∨
      hammingNorm (c.val+(octadWord F+octadWord G).val)=16 ∨
      hammingNorm (c.val+(octadWord F+octadWord G).val)=24 at ht
    change hammingNorm c.val=0 ∨ hammingNorm c.val=8 ∨ hammingNorm c.val=16 at hc
    omega
  apply Subtype.ext
  exact hammingNorm_eq_zero.mp hz

end Atlas.Fischer
