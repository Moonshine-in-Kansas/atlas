import Atlas.OrderArithmetic.PolynomialRoots.Chunk0
import Atlas.OrderArithmetic.PolynomialRoots.Chunk1
import Atlas.OrderArithmetic.PolynomialRoots.Chunk2
import Atlas.OrderArithmetic.PolynomialRoots.Chunk3
import Atlas.OrderArithmetic.PolynomialRoots.Chunk4
import Atlas.OrderArithmetic.PolynomialRoots.Chunk5

namespace Atlas.OrderArithmetic

set_option maxRecDepth 8192

theorem canonicalExceptionalPairs_root {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows)
    (hc : (r.left, r.right) ∈ canonicalExceptionalPairs) {z : ℕ} (hz : 2 ≤ z)
    (hroot : r.polynomial.eval (z : ℤ) = 0) :
    r = exceptionalInvalidBinaryRow ∧ z = 2 := by
  simp only [canonicalExceptionalPairs, Finset.mem_union] at hc
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact exceptional_pair_chunk0_root hr hc hz hroot
  · exact exceptional_pair_chunk1_root hr hc hz hroot
  · exact exceptional_pair_chunk2_root hr hc hz hroot
  · exact exceptional_pair_chunk3_root hr hc hz hroot
  · exact exceptional_pair_chunk4_root hr hc hz hroot
  · exact exceptional_pair_chunk5_root hr hc hz hroot

theorem exceptionalPolynomialRows_root_classification {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows) {z : ℕ} (hz : 2 ≤ z)
    (hroot : r.polynomial.eval (z : ℤ) = 0) :
    (r = exceptionalInvalidBinaryRow ∨ r.reverse = exceptionalInvalidBinaryRow) ∧ z = 2 := by
  have hp := (exceptional_row_membership_data hr).1
  rcases canonicalExceptionalPairs_cover (r.left, r.right) hp with hc | hc
  · obtain ⟨hr0, hz2⟩ := canonicalExceptionalPairs_root hr hc hz hroot
    exact ⟨Or.inl hr0, hz2⟩
  · have hrev : r.reverse.polynomial.eval (z : ℤ) = 0 :=
      (r.reverse_eval_eq_zero_iff (z : ℤ)).mpr hroot
    obtain ⟨hr0, hz2⟩ := canonicalExceptionalPairs_root (exceptional_row_reverse_mem hr) hc hz hrev
    exact ⟨Or.inr hr0, hz2⟩

theorem exceptionalPolynomialRows_admissible_no_root {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows) {z : ℕ} (hz : 2 ≤ z)
    (ha : r.AdmissibleAt z) : r.polynomial.eval (z : ℤ) ≠ 0 := by
  intro hroot
  obtain ⟨he, rfl⟩ := exceptionalPolynomialRows_root_classification hr hz hroot
  rcases he with he | he
  · rw [he] at ha
    exact invalidBinaryRow_not_admissible ha
  · have har : r.reverse.AdmissibleAt 2 := (r.admissibleAt_reverse 2).mpr ha
    rw [he] at har
    exact invalidBinaryRow_not_admissible har

end Atlas.OrderArithmetic
