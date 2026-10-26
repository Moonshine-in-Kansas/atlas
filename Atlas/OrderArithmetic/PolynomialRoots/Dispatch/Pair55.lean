import Atlas.OrderArithmetic.PolynomialRoots.Pair55

namespace Atlas.OrderArithmetic

theorem exceptional_pair55_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.G2 0)).divisors)
    (hy : dy ∈ (centralBound (.largeRee 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.G2 0), (.largeRee 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.G2 0), (.largeRee 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.G2 0)).divisors = ({1} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.largeRee 0)).divisors = ({1} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl
  all_goals rcases hy with rfl
  · exact exceptional_pair55_d1_d1_root hz hroot

end Atlas.OrderArithmetic
