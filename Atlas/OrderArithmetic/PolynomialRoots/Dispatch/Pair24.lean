import Atlas.OrderArithmetic.PolynomialRoots.Pair24

namespace Atlas.OrderArithmetic

theorem exceptional_pair24_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.unitary 14 0)).divisors)
    (hy : dy ∈ (centralBound (.E7 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 14 0), (.E7 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 14 0), (.E7 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.unitary 14 0)).divisors = ({1, 2, 7, 14} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.E7 0)).divisors = ({1, 2} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl
  all_goals rcases hy with rfl | rfl
  · exact exceptional_pair24_d1_d1_root hz hroot
  · exact exceptional_pair24_d1_d2_root hz hroot
  · exact exceptional_pair24_d2_d1_root hz hroot
  · exact exceptional_pair24_d2_d2_root hz hroot
  · exact exceptional_pair24_d7_d1_root hz hroot
  · exact exceptional_pair24_d7_d2_root hz hroot
  · exact exceptional_pair24_d14_d1_root hz hroot
  · exact exceptional_pair24_d14_d2_root hz hroot

end Atlas.OrderArithmetic
