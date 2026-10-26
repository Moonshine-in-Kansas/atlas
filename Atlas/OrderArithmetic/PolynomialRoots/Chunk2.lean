import Atlas.OrderArithmetic.PolynomialRoots.PairCoverage
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair20
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair21
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair22
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair23
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair24
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair25
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair26
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair27
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair28
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair29

namespace Atlas.OrderArithmetic

set_option maxRecDepth 4096 in
theorem exceptional_pair_chunk2_root {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows)
    (hc : (r.left, r.right) ∈ exceptionalPairChunk2) {z : ℕ} (hz : 2 ≤ z)
    (hroot : r.polynomial.eval (z : ℤ) = 0) :
    r = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have hd := exceptional_row_membership_data hr
  rcases r with ⟨x, y, dx, dy⟩
  change (x, y) ∈ exceptionalPairChunk2 at hc
  simp only [exceptionalPairChunk2, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  · exact exceptional_pair20_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair21_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair22_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair23_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair24_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair25_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair26_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair27_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair28_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair29_denominator_dispatch hd.2.1 hd.2.2 hz hroot

end Atlas.OrderArithmetic
