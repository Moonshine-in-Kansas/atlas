import Atlas.Fischer.GolayCoordinateSigns
import Atlas.Fischer.DuadPureTermSigns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Each nonzero calibrated word term differs from the fixed global Parker
coordinate by an actual binary sign. -/
theorem octadicWordTerm_global_sign {O : Octad} (Q : OctadCalibration O)
    (b : octadShortenedCode O) (hb : b ≠ 0)
    (hw : hammingNorm b.val.val = 8 ∨ hammingNorm b.val.val = 16) :
    ∃ e : Bit, octadicWordTerm Q b = parkerScalarSign e • golayCoordinateVector b.val hw := by
  by_cases hX : b = octadShortenedOne O
  · subst b
    rw [octadicWordTerm_one]
    apply theta_signedOctadVector_global_sixteen Q.octadLift
      (octadComplementWord O) (octadComplementWord_weight O)
    rw [Q.lift_code]
    unfold octadComplementWord
    calc
      _ = octadWord O + (golayOne + golayOne) := by rw [parkerGolay_add_self,add_zero]
      _ = _ := by abel
  · let c : OctadShortenedHyperplane O := ⟨b,hb,hX⟩
    have h8 : hammingNorm b.val.val = 8 := by
      rcases hw with h | h
      · exact h
      · exact (hX (octadShortened_weight_sixteen_eq O b h)).elim
    change ∃ e : Bit, octadicWordTerm Q c.val = parkerScalarSign e • golayCoordinateVector b.val hw
    rw [octadicWordTerm_hyperplane]
    exact signedOctadVector_global_eight (calibratedHyperplaneLift Q c) b.val h8
      (Q.parkerSection.lift_code b)

/-- Exact pure-term coefficient relative to the retained global Parker section. -/
theorem duadPureTerm_global_sign {F G : Octad}
    (hFG : (F.val ∩ G.val).card = 2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (b : octadShortenedCode G) (hb : b ≠ 0)
    (hw : hammingNorm b.val.val = 8 ∨ hammingNorm b.val.val = 16) :
    ∃ e : Bit, product (octadicWordTerm Q 0) (octadicWordTerm R b) =
      (parkerScalarSign e / 2) • golayCoordinateVector b.val hw := by
  obtain ⟨e,he⟩ := duadPureTerm_sign hFG Q R b hb
  obtain ⟨f,hf⟩ := octadicWordTerm_global_sign R b hb hw
  refine ⟨e+f,?_⟩
  rw [he,hf,smul_smul,parkerScalarSign_add]
  congr 1
  ring

end Atlas.Fischer
