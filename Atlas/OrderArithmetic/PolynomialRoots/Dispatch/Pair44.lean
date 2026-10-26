import Atlas.OrderArithmetic.PolynomialRoots.Pair44

namespace Atlas.OrderArithmetic

theorem exceptional_pair44_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.Dplus 4 0)).divisors)
    (hy : dy ∈ (centralBound (.F4 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.Dplus 4 0), (.F4 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.Dplus 4 0), (.F4 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.Dplus 4 0)).divisors = ({1, 2, 4} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.F4 0)).divisors = ({1} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl
  all_goals rcases hy with rfl
  · exact exceptional_pair44_d1_d1_root hz hroot
  · exact exceptional_pair44_d2_d1_root hz hroot
  · exact exceptional_pair44_d4_d1_root hz hroot

end Atlas.OrderArithmetic
