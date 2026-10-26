import Atlas.OrderArithmetic.PolynomialRoots.PairCoverage
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair10
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair11
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair12
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair13
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair14
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair15
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair16
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair17
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair18
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair19

namespace Atlas.OrderArithmetic

set_option maxRecDepth 4096 in
theorem exceptional_pair_chunk1_root {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows)
    (hc : (r.left, r.right) ∈ exceptionalPairChunk1) {z : ℕ} (hz : 2 ≤ z)
    (hroot : r.polynomial.eval (z : ℤ) = 0) :
    r = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have hd := exceptional_row_membership_data hr
  rcases r with ⟨x, y, dx, dy⟩
  change (x, y) ∈ exceptionalPairChunk1 at hc
  simp only [exceptionalPairChunk1, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  · exact exceptional_pair10_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair11_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair12_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair13_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair14_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair15_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair16_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair17_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair18_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair19_denominator_dispatch hd.2.1 hd.2.2 hz hroot

end Atlas.OrderArithmetic
