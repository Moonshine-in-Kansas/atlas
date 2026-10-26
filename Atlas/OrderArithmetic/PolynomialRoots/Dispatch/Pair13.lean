import Atlas.OrderArithmetic.PolynomialRoots.Pair13

namespace Atlas.OrderArithmetic

theorem exceptional_pair13_denominator_dispatch {dx dy z : ℕ}
    (hx : dx ∈ (centralBound (.unitary 4 0)).divisors)
    (hy : dy ∈ (centralBound (.trialityD4 0)).divisors)
    (hz : 2 ≤ z)
    (hroot : (⟨(.unitary 4 0), (.trialityD4 0), dx, dy⟩ : ExceptionalPolynomialRow).polynomial.eval (z : ℤ) = 0) :
    (⟨(.unitary 4 0), (.trialityD4 0), dx, dy⟩ : ExceptionalPolynomialRow) = exceptionalInvalidBinaryRow ∧ z = 2 := by
  have htx : (centralBound (.unitary 4 0)).divisors = ({1, 2, 4} : Finset ℕ) := by decide +kernel
  have hty : (centralBound (.trialityD4 0)).divisors = ({1} : Finset ℕ) := by decide +kernel
  rw [htx] at hx
  rw [hty] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl
  all_goals rcases hy with rfl
  · exact exceptional_pair13_d1_d1_root hz hroot
  · exact exceptional_pair13_d2_d1_root hz hroot
  · exact exceptional_pair13_d4_d1_root hz hroot

end Atlas.OrderArithmetic
