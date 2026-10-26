import Atlas.Rudvalis.QuaternaryEven
import Atlas.Rudvalis.TorsionMinimum
import Atlas.Codes.QuaternaryWeight

/-! Reduction of a possible small quaternary word to a single-row residue. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem quaternary_zero_residue_lower (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hne : w≠0) (hr : reduce w=0) : 24 ≤ euclideanWeight w := by
  obtain ⟨b,rfl⟩ := (reduce_eq_zero w).mp hr
  have hb := (quaternaryCode_torsion b).mp hw
  have hn : b≠0 := by intro h; apply hne; rw [h,map_zero]
  have hmin := binaryTorsion_minimum b hb hn
  rw [euclideanWeight_double]
  omega

theorem quaternary_small_weight_row (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hne : w≠0) (hsmall : euclideanWeight w<16) :
    euclideanWeight w=8 ∧ ∃ p : Point, reduce w=rowWord p := by
  have hpos : euclideanWeight w≠0 := (euclideanWeight_eq_zero w).not.mpr hne
  have hdiv := quaternaryCode_even w hw
  have hweight : euclideanWeight w=8 := by omega
  refine ⟨hweight,?_⟩
  have hr : reduce w≠0 := by
    intro hz
    have := quaternary_zero_residue_lower w hw hne hz
    omega
  have hmem : reduce w∈binaryResidue := (quaternaryCode_residue _).mpr ⟨w,hw,rfl⟩
  have hlow := binaryResidue_minimum _ hmem hr
  have hupp := residue_weight_le w
  have heq : hammingNorm (reduce w)=8 := by omega
  exact (binaryResidue_weight_eight_iff _ hmem).mp heq

end Atlas.Rudvalis
