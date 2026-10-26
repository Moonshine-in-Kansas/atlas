import Atlas.OrderArithmetic.PolynomialRoots.Pair06

namespace Atlas.OrderArithmetic

theorem exceptional_pair06_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.linear 5 0)).divisors)
    (hy : dy ∈ (centralBound (.twistedE6 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.linear 5 0), (.twistedE6 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.linear 5 0), (.twistedE6 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.linear 5 0)).divisors = ({1, 5} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.twistedE6 0)).divisors = ({1, 3} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  all_goals rcases hy with rfl | rfl
  · exact exceptional_pair06_d1_d1_root hz hroot
  · exact exceptional_pair06_d1_d3_root hz hroot
  · exact exceptional_pair06_d5_d1_root hz hroot
  · exact exceptional_pair06_d5_d3_root hz hroot

end Atlas.OrderArithmetic
