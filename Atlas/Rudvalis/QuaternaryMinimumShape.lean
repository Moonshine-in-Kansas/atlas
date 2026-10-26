import Atlas.Rudvalis.QuaternaryMinimum
import Atlas.Codes.QuaternaryWeightSplit

/-! Every minimum quaternary word has sixteen odd entries and no twos. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem quaternary_minimum_residue_weight (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) : hammingNorm (reduce w)=16 := by
  have hne : w≠0 := by intro hz; have := (euclideanWeight_eq_zero w).mpr hz; omega
  have hr : reduce w≠0 := by
    intro hz
    have := quaternary_zero_residue_lower w hw hne hz
    omega
  have hm : reduce w∈binaryResidue := (quaternaryCode_residue _).mpr ⟨w,hw,rfl⟩
  have hl := binaryResidue_minimum _ hm hr
  have hu := residue_weight_le w
  by_contra h
  have hs : hammingNorm (reduce w)<16 := by omega
  have he : hammingNorm (reduce w)=8 := by
    obtain ⟨a,ha⟩ := hm
    obtain ⟨hM,hc⟩ := binaryNormalMap_small_parameters a (by rwa [ha])
    have hp : a=(a.1,0,0) := Prod.ext rfl (Prod.ext hM hc)
    have he := binaryNormalMap_constant_weight a.1
    rw [← hp,ha] at he
    omega
  obtain ⟨p,hp⟩ := (binaryResidue_weight_eight_iff _ hm).mp he
  have := quaternary_row_lift_lower w hw p hp
  omega

theorem quaternary_minimum_no_twos (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) : ∀ z,w z≠2 :=
  (euclideanWeight_eq_residue_iff w).mp (hweight.trans (quaternary_minimum_residue_weight w hw hweight).symm)

theorem quaternary_minimum_symbols (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) (z : Coordinate) : w z=0 ∨ w z=1 ∨ w z= -1 := by
  have h : ∀ a : Quat, a≠2 → a=0 ∨ a=1 ∨ a= -1 := by decide +kernel
  exact h _ (quaternary_minimum_no_twos w hw hweight z)

end Atlas.Rudvalis
