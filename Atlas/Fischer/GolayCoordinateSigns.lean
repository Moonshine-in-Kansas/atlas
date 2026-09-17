import Atlas.Fischer.GolayCoordinateVectors
import Atlas.Fischer.SignedOctadProductFormulas

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Two actual signed octads over the same codeword differ by their actual
Parker sign-bit difference. -/
theorem signedOctadVector_same_code (d f : SignedOctad) (h : d.val.1=f.val.1) :
    signedOctadVector d=parkerScalarSign (d.val.2+f.val.2) • signedOctadVector f := by
  have hs : signedOctadSupport d=signedOctadSupport f := by
    apply Subtype.ext
    exact congrArg (fun c : golay => support c.val) h
  rw [signedOctadVector,signedOctadVector,hs,smul_smul,parkerScalarSign_add]
  rw [mul_assoc,parkerScalarSign_square,mul_one]

theorem signedOctadVector_global_eight (d : SignedOctad) (c : golay)
    (hc : hammingNorm c.val=8) (hd : d.val.1=c) :
    ∃ e : Bit, signedOctadVector d=parkerScalarSign e • golayCoordinateVector c (Or.inl hc) := by
  refine ⟨d.val.2+0,?_⟩
  rw [golayCoordinateVector,dif_pos hc]
  exact signedOctadVector_same_code d ⟨(c,0),hc⟩ hd

theorem theta_signedOctadVector_global_sixteen (d : SignedOctad) (c : golay)
    (hc : hammingNorm c.val=16) (hd : d.val.1=c+golayOne) :
    ∃ e : Bit, theta • signedOctadVector d=
      parkerScalarSign e • golayCoordinateVector c (Or.inr hc) := by
  let f : SignedOctad := ⟨parkerLoopMultiply (c,0) parkerOmega,golayComplement_weight_sixteen c hc⟩
  refine ⟨d.val.2+f.val.2,?_⟩
  rw [golayCoordinateVector,dif_neg (by omega)]
  change theta • signedOctadVector d=parkerScalarSign (d.val.2+f.val.2) • (theta • signedOctadVector f)
  rw [signedOctadVector_same_code d f hd,smul_comm]

end Atlas.Fischer
