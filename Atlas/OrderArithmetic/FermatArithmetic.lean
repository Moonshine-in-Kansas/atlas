import Atlas.OrderArithmetic.Normalization
import Atlas.OrderArithmetic.ElementaryReduction
import Mathlib.Tactic.Ring

namespace Atlas.OrderArithmetic

/-- Literal degree-two formula, retaining its central divisor. -/
theorem linear_two_order (q : ℕ) :
    order (.linear 2 q) = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
  simp [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem linear_two_even_order {q : ℕ} (hq : 2 ≤ q) (he : Even q) :
    order (.linear 2 q) = q * (q ^ 2 - 1) := by
  have ho : Odd (q - 1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  rw [linear_two_order, ho.coprime_two_left.gcd_eq_one, Nat.div_one]

/-- The Fermat-side adjacent degree-two equation has exactly the parameter q=4.
No dominance theorem or finite list of Fermat primes is assumed. -/
theorem fermat_adjacent_linear_two {q : ℕ} (hq : 4 ≤ q) (hev : Even q)
    (he : order (.linear 2 q) = order (.linear 2 (q + 1))) : q = 4 := by
  have hd : Nat.gcd 2 q = 2 := Nat.gcd_eq_left (even_iff_two_dvd.mp hev)
  rw [linear_two_even_order (by omega) hev, linear_two_order] at he
  simp only [Nat.add_sub_cancel, hd] at he
  have hdiv : 2 ∣ (q + 1) * ((q + 1) ^ 2 - 1) := by
    have hh : (q + 1) ^ 2 - 1 = q * (q + 2) := by
      have hs := Nat.sub_add_cancel (show 1 ≤ (q + 1) ^ 2 by nlinarith)
      nlinarith
    rw [hh]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (even_iff_two_dvd.mp hev) _) _
  have hmul := Nat.div_mul_cancel hdiv
  rw [← he] at hmul
  have hs := Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)
  have hs' := Nat.sub_add_cancel (show 1 ≤ (q + 1) ^ 2 by nlinarith)
  by_contra hn
  have hsub := Nat.sub_add_cancel hq
  have hlt : 0 < q - 4 := by omega
  have hpos : 0 < q * (q + 1) * (q - 4) := by positivity
  nlinarith

/-- The adjacent prime occurs to exactly the first power in the even-field order. -/
theorem fermat_adjacent_valuation {q : ℕ} (hq : 4 ≤ q) (hev : Even q)
    (hp : (q + 1).Prime) : (order (.linear 2 q)).factorization (q + 1) = 1 := by
  have hq0 : q ≠ 0 := by omega
  have hm0 : q - 1 ≠ 0 := by omega
  have hnq : ¬ q + 1 ∣ q := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hnm : ¬ q + 1 ∣ q - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hs : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have := Nat.sub_add_cancel (show 1 ≤ q by omega)
    have := Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)
    nlinarith
  rw [linear_two_even_order (by omega) hev, hs, ← mul_assoc,
    Nat.factorization_mul (mul_ne_zero hq0 hm0) hp.ne_zero,
    Nat.factorization_mul hq0 hm0]
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnq,
    Nat.factorization_eq_zero_of_not_dvd hnm, hp.factorization_self, zero_add]

/-- Once the competitor's characteristic is the adjacent prime, the only match
is L₂(4)/L₂(5). The characteristic hypothesis remains explicit. -/
theorem fermat_adjacent_characteristic_match {x : RawEntry} {q f : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hq : 4 ≤ q) (hev : Even q)
    (hp : (q + 1).Prime) (hf : 1 ≤ f) (hfield : fieldSize x = (q + 1) ^ f)
    (he : order (.linear 2 q) = order x) : q = 4 ∧ x = .linear 2 5 := by
  have hv := order_characteristic_valuation hx hl hp hf hfield
  rw [← he, fermat_adjacent_valuation hq hev hp] at hv
  have ha := characteristicExponent_pos hx hl
  have hf1 : f = 1 := by nlinarith
  have ha1 : characteristicExponent x = 1 := by nlinarith
  obtain ⟨r, rfl⟩ := exponent_one_linear_two hx hl ha1
  have hr : r = q + 1 := by simpa [fieldSize, hf1] using hfield
  subst r
  have hq4 := fermat_adjacent_linear_two hq hev he
  exact ⟨hq4, by rw [hq4]⟩

end Atlas.OrderArithmetic

