import Atlas.OrderArithmetic.PolynomialRoots.PairCoverage
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair40
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair41
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair42
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair43
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair44
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair45
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair46
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair47
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair48
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair49

namespace Atlas.OrderArithmetic

set_option maxRecDepth 4096 in
theorem exceptional_pair_chunk4_root {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows)
    (hc : (r.left, r.right) ∈ exceptionalPairChunk4) {z : ℕ} (hz : 2 ≤ z)
    (hroot : r.polynomial.eval (z : ℤ) = 0) :
    r = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have hd := exceptional_row_membership_data hr
  rcases r with ⟨x, y, dx, dy⟩
  change (x, y) ∈ exceptionalPairChunk4 at hc
  simp only [exceptionalPairChunk4, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  · exact exceptional_pair40_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair41_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair42_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair43_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair44_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair45_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair46_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair47_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair48_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair49_denominator_dispatch hd.2.1 hd.2.2 hz hroot

end Atlas.OrderArithmetic
