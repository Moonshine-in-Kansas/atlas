import Atlas.OrderArithmetic.ExceptionalRowCounts

namespace Atlas.OrderArithmetic
open Polynomial

def ExceptionalPolynomialRow.reverse (r : ExceptionalPolynomialRow) : ExceptionalPolynomialRow :=
  ⟨r.right, r.left, r.rightDenominator, r.leftDenominator⟩

@[simp] theorem ExceptionalPolynomialRow.reverse_reverse (r : ExceptionalPolynomialRow) :
    r.reverse.reverse = r := by
  cases r
  rfl

@[simp] theorem ExceptionalPolynomialRow.leftExponent_reverse (r : ExceptionalPolynomialRow) :
    r.reverse.leftExponent = r.rightExponent := by
  simp only [reverse, leftExponent, rightExponent, Nat.gcd_comm]

@[simp] theorem ExceptionalPolynomialRow.rightExponent_reverse (r : ExceptionalPolynomialRow) :
    r.reverse.rightExponent = r.leftExponent := by
  simp only [reverse, leftExponent, rightExponent, Nat.gcd_comm]

theorem ExceptionalPolynomialRow.polynomial_reverse (r : ExceptionalPolynomialRow) :
    r.reverse.polynomial = -r.polynomial := by
  simp only [polynomial, leftExponent_reverse, rightExponent_reverse]
  simp only [reverse, comparisonPolynomial]
  ring

@[simp] theorem ExceptionalPolynomialRow.reverse_eval_eq_zero_iff
    (r : ExceptionalPolynomialRow) (z : ℤ) :
    r.reverse.polynomial.eval z = 0 ↔ r.polynomial.eval z = 0 := by
  rw [polynomial_reverse, eval_neg, neg_eq_zero]

set_option maxRecDepth 4096 in
theorem exceptional_pair_swap_mem {x y : RawEntry}
    (h : (x, y) ∈ exceptionalPairCandidates) : (y, x) ∈ exceptionalPairCandidates := by
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp h
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hmem
  obtain ⟨hex, hax, hay, hrx, hry, hratio, hne⟩ := hc
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨hy, hx⟩,
    ⟨hex.symm, hay, hax, hry, hrx, hratio.symm, Ne.symm hne⟩⟩

set_option maxRecDepth 4096 in
theorem exceptional_row_reverse_mem {r : ExceptionalPolynomialRow}
    (h : r ∈ exceptionalPolynomialRows) : r.reverse ∈ exceptionalPolynomialRows := by
  obtain ⟨hxy, hx, hy⟩ := exceptional_row_membership_data h
  exact mem_exceptionalPolynomialRows (exceptional_pair_swap_mem hxy) hy hx

def ExceptionalPolynomialRow.AdmissibleAt (r : ExceptionalPolynomialRow) (z : ℕ) : Prop :=
  Admissible (withField r.left (z ^ r.leftExponent)) ∧
    Admissible (withField r.right (z ^ r.rightExponent))

@[simp] theorem ExceptionalPolynomialRow.admissibleAt_reverse (r : ExceptionalPolynomialRow)
    (z : ℕ) : r.reverse.AdmissibleAt z ↔ r.AdmissibleAt z := by
  simp only [AdmissibleAt, leftExponent, rightExponent, reverse, Nat.gcd_comm, and_comm]

/-- The sole candidate integer root from the polynomial diagnostics; whether it
is the sole root is proved separately by the finite certificates. -/
def exceptionalInvalidBinaryRow : ExceptionalPolynomialRow :=
  ⟨.unitary 3 0, .smallRee 0, 3, 1⟩

theorem invalidBinaryRow_not_admissible : ¬ exceptionalInvalidBinaryRow.AdmissibleAt 2 := by
  intro h
  have hx := h.1
  change Admissible (.unitary 3 2) at hx
  exact hx.2.2 ⟨rfl, rfl⟩

end Atlas.OrderArithmetic
