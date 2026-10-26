import Atlas.OrderArithmetic.PolynomialRoots.PairCoverage
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair50
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair51
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair52
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair53
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair54
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair55
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair56
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair57
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair58

namespace Atlas.OrderArithmetic

set_option maxRecDepth 4096 in
theorem exceptional_pair_chunk5_root {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows)
    (hc : (r.left, r.right) ∈ exceptionalPairChunk5) {z : ℕ} (hz : 2 ≤ z)
    (hroot : r.polynomial.eval (z : ℤ) = 0) :
    r = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have hd := exceptional_row_membership_data hr
  rcases r with ⟨x, y, dx, dy⟩
  change (x, y) ∈ exceptionalPairChunk5 at hc
  simp only [exceptionalPairChunk5, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  · exact exceptional_pair50_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair51_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair52_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair53_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair54_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair55_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair56_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair57_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair58_denominator_dispatch hd.2.1 hd.2.2 hz hroot

end Atlas.OrderArithmetic
