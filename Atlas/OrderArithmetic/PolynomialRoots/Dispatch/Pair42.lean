import Atlas.OrderArithmetic.PolynomialRoots.Pair42

namespace Atlas.OrderArithmetic

theorem exceptional_pair42_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.C 7 0)).divisors)
    (hy : dy ∈ (centralBound (.E7 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.C 7 0), (.E7 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.C 7 0), (.E7 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.C 7 0)).divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.E7 0)).divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  all_goals rcases hy with rfl | rfl
  · exact exceptional_pair42_d1_d1_root hz hroot
  · exact exceptional_pair42_d1_d2_root hz hroot
  · exact exceptional_pair42_d2_d1_root hz hroot
  · exact exceptional_pair42_d2_d2_root hz hroot

end Atlas.OrderArithmetic
