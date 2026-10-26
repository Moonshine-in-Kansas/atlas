import Atlas.Rudvalis.QuaternarySmallWeight
import Atlas.Rudvalis.BlockParity
import Atlas.Rudvalis.QuaternarySeedWeights

/-! Exact Euclidean minimum of the actual Version 33 quaternary code. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem quaternaryCode_minimum (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hne : w≠0) : 16 ≤ euclideanWeight w := by
  by_contra h
  have hsmall : euclideanWeight w<16 := by omega
  obtain ⟨hweight,p,hp⟩ := quaternary_small_weight_row w hw hne hsmall
  have hlower := quaternary_row_lift_lower w hw p hp
  omega

theorem quaternaryCode_minimum_exact :
    (∀ w : QuaternaryWord, w∈quaternaryCode → w≠0 → 16 ≤ euclideanWeight w) ∧
      ∃ w : QuaternaryWord, w∈quaternaryCode ∧ w≠0 ∧ euclideanWeight w=16 := by
  refine ⟨quaternaryCode_minimum, ?_⟩
  obtain ⟨w,hw,hweight⟩ := quaternaryCode_weight_sixteen_exists
  refine ⟨w,hw, ?_,hweight⟩
  intro hzero
  have he : euclideanWeight w=0 := (euclideanWeight_eq_zero w).mpr hzero
  omega

end Atlas.Rudvalis
