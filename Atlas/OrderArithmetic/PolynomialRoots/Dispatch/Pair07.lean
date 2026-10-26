import Atlas.OrderArithmetic.PolynomialRoots.Pair07

namespace Atlas.OrderArithmetic

theorem exceptional_pair07_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.linear 7 0)).divisors)
    (hy : dy ∈ (centralBound (.E6 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.linear 7 0), (.E6 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.linear 7 0), (.E6 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.linear 7 0)).divisors = ({1, 7} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.E6 0)).divisors = ({1, 3} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  all_goals rcases hy with rfl | rfl
  · exact exceptional_pair07_d1_d1_root hz hroot
  · exact exceptional_pair07_d1_d3_root hz hroot
  · exact exceptional_pair07_d7_d1_root hz hroot
  · exact exceptional_pair07_d7_d3_root hz hroot

end Atlas.OrderArithmetic
