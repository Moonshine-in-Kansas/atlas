import Atlas.OrderArithmetic.PolynomialRoots.Pair00

namespace Atlas.OrderArithmetic

theorem exceptional_pair00_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.linear 2 0)).divisors)
    (hy : dy ∈ (centralBound (.suzuki 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.linear 2 0), (.suzuki 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.linear 2 0), (.suzuki 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.linear 2 0)).divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.suzuki 0)).divisors = ({1} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  all_goals rcases hy with rfl
  · exact exceptional_pair00_d1_d1_root hz hroot
  · exact exceptional_pair00_d2_d1_root hz hroot

end Atlas.OrderArithmetic
