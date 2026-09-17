import Atlas.Fischer.OctadQuadrilateralWeight
import Atlas.Fischer.CubicCompletionIntersections

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The fourth triangle type is the parity sum of the first three types.
This is an equality of actual Leech-code diamond constructions. -/
theorem cubicQuadrilateral_delta (D F G : Octad)
    (hDF : OctadPairAdmissible D F) (hDG : OctadPairAdmissible D G)
    (hFG : OctadPairAdmissible F G) :
    octadDelta (octadDiamond D F hDF) (octadDiamond D G hDG) =
      (octadDelta D F + octadDelta D G + octadDelta F G) % 2 := by
  let B := octadDiamond D F hDF
  let C := octadDiamond D G hDG
  let I := octadDiamond F G hFG
  let n := (octadDelta D F + octadDelta D G + octadDelta F G) % 2
  have hw : octadWord I = octadWord B + octadWord C +
      if n = 1 then golayOne else 0 := by
    dsimp [I,B,C,n]
    rw [octadDiamond_word,octadDiamond_word,octadDiamond_word]
    rcases hDF with hf | hf <;> rcases hDG with hg | hg <;> rcases hFG with hk | hk <;>
      simp only [octadDelta,hf,hg,hk,show (4 : ℕ) ≠ 0 by decide,ite_false,ite_true] <;>
      norm_num <;> abel_nf <;>
      simp [show (2 : ℤ) • (octadWord D) = 0 by rw [show (2 : ℤ) = 1 + 1 by rfl,add_zsmul,one_zsmul,parkerGolay_add_self], show (2 : ℤ) • golayOne = 0 by rw [show (2 : ℤ) = 1 + 1 by rfl,add_zsmul,one_zsmul,parkerGolay_add_self]]
  have hn : n < 2 := Nat.mod_lt _ (by decide)
  by_cases he : n = 1
  · rw [if_pos he] at hw
    have hc := octadWord_complementary_sum_weight I B C hw
    have hc' : (B.val ∩ C.val).card = 0 := by
      simpa only [signedOctadIntersection,signedOctadSupport_canonical] using hc
    change octadDelta B C = n
    simp [octadDelta,hc',he]
  · rw [if_neg he,add_zero] at hw
    have hc := octadWord_sum_weight I B C hw
    have hc' : (B.val ∩ C.val).card = 4 := by
      simpa only [signedOctadIntersection,signedOctadSupport_canonical] using hc
    change octadDelta B C = n
    have hn0 : n = 0 := by omega
    simp [octadDelta,hc',hn0]

end Atlas.Fischer
