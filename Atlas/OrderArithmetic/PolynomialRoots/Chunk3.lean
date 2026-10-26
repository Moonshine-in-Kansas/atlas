import Atlas.OrderArithmetic.PolynomialRoots.PairCoverage
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair30
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair31
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair32
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair33
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair34
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair35
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair36
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair37
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair38
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair39

namespace Atlas.OrderArithmetic

set_option maxRecDepth 4096 in
theorem exceptional_pair_chunk3_root {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows)
    (hc : (r.left, r.right) ∈ exceptionalPairChunk3) {z : ℕ} (hz : 2 ≤ z)
    (hroot : r.polynomial.eval (z : ℤ) = 0) :
    r = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have hd := exceptional_row_membership_data hr
  rcases r with ⟨x, y, dx, dy⟩
  change (x, y) ∈ exceptionalPairChunk3 at hc
  simp only [exceptionalPairChunk3, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  · exact exceptional_pair30_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair31_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair32_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair33_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair34_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair35_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair36_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair37_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair38_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair39_denominator_dispatch hd.2.1 hd.2.2 hz hroot

end Atlas.OrderArithmetic
