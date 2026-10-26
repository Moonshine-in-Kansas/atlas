import Atlas.OrderArithmetic.PolynomialRoots.Pair32

namespace Atlas.OrderArithmetic

theorem exceptional_pair32_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.B 4 0)).divisors)
    (hy : dy ∈ (centralBound (.twistedE6 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.B 4 0), (.twistedE6 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.B 4 0), (.twistedE6 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.B 4 0)).divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.twistedE6 0)).divisors = ({1, 3} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  all_goals rcases hy with rfl | rfl
  · exact exceptional_pair32_d1_d1_root hz hroot
  · exact exceptional_pair32_d1_d3_root hz hroot
  · exact exceptional_pair32_d2_d1_root hz hroot
  · exact exceptional_pair32_d2_d3_root hz hroot

end Atlas.OrderArithmetic
