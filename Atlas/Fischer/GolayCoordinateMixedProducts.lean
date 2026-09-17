import Atlas.Fischer.GolayCoordinateProductSigns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Weight-eight global vectors multiply with the source half-coordinate factor
in both admissible sum-weight branches. -/
theorem golayCoordinateVector_eight_eight (b c : golay)
    (hb : hammingNorm b.val=8) (hc : hammingNorm c.val=8)
    (hs : hammingNorm (b+c).val=8 ∨ hammingNorm (b+c).val=16) :
    ∃ e : Bit, product (golayCoordinateVector b (Or.inl hb))
      (golayCoordinateVector c (Or.inl hc))=
      (parkerScalarSign e / 2) • golayCoordinateVector (b+c) hs := by
  rw [golayCoordinateVector,dif_pos hb,golayCoordinateVector,dif_pos hc]
  rcases hs with h8 | h16
  · exact product_signedOctads_global_eight ⟨(b,0),hb⟩ ⟨(c,0),hc⟩ (b+c) h8 rfl
  · exact product_signedOctads_global_sixteen ⟨(b,0),hb⟩ ⟨(c,0),hc⟩ (b+c) h16 rfl

/-- The admissible weight16+8 mixed branch, with the actual global Omega signs. -/
theorem golayCoordinateVector_sixteen_eight (b c : golay)
    (hb : hammingNorm b.val=16) (hc : hammingNorm c.val=8)
    (hs : hammingNorm (b+c).val=16) :
    ∃ e : Bit, product (golayCoordinateVector b (Or.inr hb))
      (golayCoordinateVector c (Or.inl hc))=
      (parkerScalarSign e / 2) • golayCoordinateVector (b+c) (Or.inr hs) := by
  rw [golayCoordinateVector,dif_neg (by omega),golayCoordinateVector,dif_pos hc]
  apply product_theta_signedOctad_global_sixteen _ _ _ hs
  change (b+golayOne)+c=(b+c)+golayOne
  abel

/-- The reversed mixed branch follows from the actual commutative product. -/
theorem golayCoordinateVector_eight_sixteen (b c : golay)
    (hb : hammingNorm b.val=8) (hc : hammingNorm c.val=16)
    (hs : hammingNorm (b+c).val=16) :
    ∃ e : Bit, product (golayCoordinateVector b (Or.inl hb))
      (golayCoordinateVector c (Or.inr hc))=
      (parkerScalarSign e / 2) • golayCoordinateVector (b+c) (Or.inr hs) := by
  rw [product_comm]
  have hswap : hammingNorm (c+b).val=16 := by simpa only [add_comm c b] using hs
  obtain ⟨e,he⟩ := golayCoordinateVector_sixteen_eight c b hc hb hswap
  refine ⟨e,he.trans ?_⟩
  congr 2
  exact add_comm c b

end Atlas.Fischer
