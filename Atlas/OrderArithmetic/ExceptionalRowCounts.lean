import Atlas.OrderArithmetic.ExceptionalPolynomialRows

namespace Atlas.OrderArithmetic

/-! Kernel-computed cardinalities of the finite exceptional row universe.
These counts do not assert coefficient certificates or exclude polynomial roots. -/

set_option maxRecDepth 16384 in
theorem exceptionalRankTemplates_card : exceptionalRankTemplates.card = 58 := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem exceptionalPairCandidates_card : exceptionalPairCandidates.card = 118 := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem exceptionalPolynomialRows_card : exceptionalPolynomialRows.card = 416 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem exceptional_row_membership_data {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows) :
    (r.left, r.right) ∈ exceptionalPairCandidates ∧
    r.leftDenominator ∈ (centralBound r.left).divisors ∧
    r.rightDenominator ∈ (centralBound r.right).divisors := by
  obtain ⟨⟨x, y⟩, hxy, hrow⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨⟨dx, dy⟩, hdiv, rfl⟩ := Finset.mem_image.mp hrow
  exact ⟨hxy, (Finset.mem_product.mp hdiv).1, (Finset.mem_product.mp hdiv).2⟩

set_option maxRecDepth 4096 in
theorem exceptional_row_condition {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows) : ExceptionalPairCondition (r.left, r.right) := by
  have hp := (exceptional_row_membership_data hr).1
  exact (Finset.mem_filter.mp hp).2

set_option maxRecDepth 4096 in
theorem exceptional_row_distinct {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows) : r.left ≠ r.right := by
  obtain ⟨_, _, _, _, _, _, hne⟩ := exceptional_row_condition hr
  exact hne

set_option maxRecDepth 4096 in
theorem exceptional_row_denominators_pos {r : ExceptionalPolynomialRow}
    (hr : r ∈ exceptionalPolynomialRows) :
    0 < r.leftDenominator ∧ 0 < r.rightDenominator := by
  obtain ⟨_, hx, hy⟩ := exceptional_row_membership_data hr
  exact ⟨Nat.pos_of_mem_divisors hx, Nat.pos_of_mem_divisors hy⟩

end Atlas.OrderArithmetic
