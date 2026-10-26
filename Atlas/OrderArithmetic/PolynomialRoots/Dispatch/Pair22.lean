import Atlas.OrderArithmetic.PolynomialRoots.Pair22

namespace Atlas.OrderArithmetic

theorem exceptional_pair22_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.unitary 12 0)).divisors)
    (hy : dy ∈ (centralBound (.E6 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 12 0), (.E6 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 12 0), (.E6 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.unitary 12 0)).divisors = ({1, 2, 3, 4, 6, 12} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.E6 0)).divisors = ({1, 3} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hy with rfl | rfl
  · exact exceptional_pair22_d1_d1_root hz hroot
  · exact exceptional_pair22_d1_d3_root hz hroot
  · exact exceptional_pair22_d2_d1_root hz hroot
  · exact exceptional_pair22_d2_d3_root hz hroot
  · exact exceptional_pair22_d3_d1_root hz hroot
  · exact exceptional_pair22_d3_d3_root hz hroot
  · exact exceptional_pair22_d4_d1_root hz hroot
  · exact exceptional_pair22_d4_d3_root hz hroot
  · exact exceptional_pair22_d6_d1_root hz hroot
  · exact exceptional_pair22_d6_d3_root hz hroot
  · exact exceptional_pair22_d12_d1_root hz hroot
  · exact exceptional_pair22_d12_d3_root hz hroot

end Atlas.OrderArithmetic
