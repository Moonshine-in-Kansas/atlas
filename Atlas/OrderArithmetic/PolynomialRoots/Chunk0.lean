import Atlas.OrderArithmetic.PolynomialRoots.PairCoverage
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair00
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair01
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair02
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair03
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair04
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair05
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair06
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair07
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair08
import Atlas.OrderArithmetic.PolynomialRoots.Dispatch.Pair09

namespace Atlas.OrderArithmetic

set_option maxRecDepth 4096 in
theorem exceptional_pair_chunk0_root {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows)
    (hc : (r.left, r.right) ∈ exceptionalPairChunk0) {z : ℕ} (hz : 2 ≤ z)
    (hroot : r.polynomial.eval (z : ℤ) = 0) :
    r = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have hd := exceptional_row_membership_data hr
  rcases r with ⟨x, y, dx, dy⟩
  change (x, y) ∈ exceptionalPairChunk0 at hc
  simp only [exceptionalPairChunk0, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  · exact exceptional_pair00_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair01_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair02_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair03_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair04_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair05_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair06_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair07_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair08_denominator_dispatch hd.2.1 hd.2.2 hz hroot
  · exact exceptional_pair09_denominator_dispatch hd.2.1 hd.2.2 hz hroot

end Atlas.OrderArithmetic
