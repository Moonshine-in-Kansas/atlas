import Atlas.Fischer.OctadicWordGlobalSigns
import Atlas.Fischer.GolayCoordinateMixedProducts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Every admissible nonzero/nonzero word term of an actual intersecting-octad
pair has the exact source magnitude one half, with its sign derived from the
calibrated Parker labels. -/
theorem duadMixedTerm_global_sign {F G : Octad}
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (b : octadShortenedCode F) (c : octadShortenedCode G) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hs : hammingNorm (b.val+c.val).val=8 ∨ hammingNorm (b.val+c.val).val=16) :
    ∃ e : Bit, product (octadicWordTerm Q b) (octadicWordTerm R c)=
      (parkerScalarSign e / 2) • golayCoordinateVector (b.val+c.val) hs := by
  have hb : hammingNorm b.val.val=8 ∨ hammingNorm b.val.val=16 :=
    (octadShortened_weights F b).resolve_left (fun h =>
      hb0 (Subtype.ext (Subtype.ext (hammingNorm_eq_zero.mp h))))
  have hc : hammingNorm c.val.val=8 ∨ hammingNorm c.val.val=16 :=
    (octadShortened_weights G c).resolve_left (fun h =>
      hc0 (Subtype.ext (Subtype.ext (hammingNorm_eq_zero.mp h))))
  obtain ⟨eb,heb⟩ := octadicWordTerm_global_sign Q b hb0 hb
  obtain ⟨ec,hec⟩ := octadicWordTerm_global_sign R c hc0 hc
  have hp : ∃ e : Bit, product (golayCoordinateVector b.val hb) (golayCoordinateVector c.val hc)=
      (parkerScalarSign e / 2) • golayCoordinateVector (b.val+c.val) hs := by
    rcases hb with hb8 | hb16 <;> rcases hc with hc8 | hc16
    · exact golayCoordinateVector_eight_eight b.val c.val hb8 hc8 hs
    · have hn : hammingNorm (b.val+c.val).val ≠ 8 := by
        have h := duadPair_mixed_weight_not_eight G F (by simpa [Finset.inter_comm] using hFG) b hb8
        rw [octadShortened_weight_sixteen_eq G c hc16]
        change hammingNorm (b.val+octadComplementWord G).val ≠ 8
        simpa only [add_comm] using h
      exact golayCoordinateVector_eight_sixteen b.val c.val hb8 hc16 (hs.resolve_left hn)
    · have hn : hammingNorm (b.val+c.val).val ≠ 8 := by
        rw [octadShortened_weight_sixteen_eq F b hb16]
        exact duadPair_mixed_weight_not_eight F G hFG c hc8
      exact golayCoordinateVector_sixteen_eight b.val c.val hb16 hc8 (hs.resolve_left hn)
    · have h12 := duadPair_complement_sum_weight F G hFG
      rw [octadShortened_weight_sixteen_eq F b hb16,
        octadShortened_weight_sixteen_eq G c hc16] at hs
      change hammingNorm (octadComplementWord F+octadComplementWord G).val=8 ∨
        hammingNorm (octadComplementWord F+octadComplementWord G).val=16 at hs
      omega
  obtain ⟨e,he⟩ := hp
  refine ⟨eb+ec+e,?_⟩
  rw [heb,hec,product_smul_left,product_smul_right,parkerScalarSign_star,
    parkerScalarSign_star,he]
  simp only [smul_smul,parkerScalarSign_add]
  congr 1
  ring

end Atlas.Fischer
