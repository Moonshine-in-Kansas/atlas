import Atlas.OrderArithmetic.PolynomialRoots.Pair31

namespace Atlas.OrderArithmetic

theorem exceptional_pair31_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.B 4 0)).divisors)
    (hy : dy ∈ (centralBound (.F4 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.B 4 0), (.F4 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.B 4 0), (.F4 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.B 4 0)).divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.F4 0)).divisors = ({1} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  all_goals rcases hy with rfl
  · exact exceptional_pair31_d1_d1_root hz hroot
  · exact exceptional_pair31_d2_d1_root hz hroot

end Atlas.OrderArithmetic
