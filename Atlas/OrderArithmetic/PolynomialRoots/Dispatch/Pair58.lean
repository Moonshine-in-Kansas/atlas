import Atlas.OrderArithmetic.PolynomialRoots.Pair58

namespace Atlas.OrderArithmetic

theorem exceptional_pair58_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.suzuki 0)).divisors)
    (hy : dy ∈ (centralBound (.smallRee 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.suzuki 0), (.smallRee 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.suzuki 0), (.smallRee 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.suzuki 0)).divisors = ({1} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.smallRee 0)).divisors = ({1} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl
  all_goals rcases hy with rfl
  · exact exceptional_pair58_d1_d1_root hz hroot

end Atlas.OrderArithmetic
