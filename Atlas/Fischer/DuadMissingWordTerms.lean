import Atlas.Fischer.GolayMissingEigenspaces
import Atlas.Fischer.DuadWordPairCoordinates

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem duadShortened_weights (p : Finset Omega) (hp : p.card = 2)
    (c : duadShortenedCode p) :
    hammingNorm c.val.val = 0 ∨ hammingNorm c.val.val = 8 ∨
      hammingNorm c.val.val = 12 ∨ hammingNorm c.val.val = 16 := by
  have hw := golay_weights c.val
  have h24 : hammingNorm c.val.val ≠ 24 := by
    intro h
    have hc := (weight_twentyfour_iff c.val.val).mp h
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < p.card by omega)
    have hz := (mem_duadShortenedCode p c.val).mp c.property i hi
    rw [hc] at hz
    change (1 : Bit) = 0 at hz
    exact one_ne_zero hz
  omega

/-- Every nonzero omitted shortened-duad word is a dodecad, so its individual
product term vanishes in the actual coordinate algebra. -/
theorem duadWordPair_missing_zero (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (c : duadShortenedCode p) (hc : c ≠ 0)
    (hw : ¬ (hammingNorm c.val.val = 8 ∨ hammingNorm c.val.val = 16)) :
    product (octadicWordTerm Q ((duadOctadSumEquiv p hp F G hFG).symm c).1)
      (octadicWordTerm R ((duadOctadSumEquiv p hp F G hFG).symm c).2) = 0 := by
  have h0 : hammingNorm c.val.val ≠ 0 := by
    intro h
    apply hc
    exact Subtype.ext (Subtype.ext (hammingNorm_eq_zero.mp h))
  have h12 : hammingNorm c.val.val = 12 := by
    have h := duadShortened_weights p hp c
    omega
  apply golayCommonEigenvector_weight_twelve_zero c.val h12
  have hs := (duadOctadSumEquiv p hp F G hFG).apply_symm_apply c
  have hv := congrArg Subtype.val hs
  rw [duadOctadSumEquiv_apply] at hv
  rw [← hv]
  exact octadicWordTerm_product_eigenvector Q R _ _

end Atlas.Fischer
