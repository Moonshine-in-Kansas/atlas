import Atlas.OrderArithmetic.FermatArithmetic

namespace Atlas.OrderArithmetic

/-- An odd prime-power divisor of q²-1 lies wholly in one adjacent factor. -/
theorem odd_prime_power_dvd_adjacent {l e q : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hq : 2 ≤ q) (hd : l ^ e ∣ q ^ 2 - 1) :
    l ^ e ∣ q - 1 ∨ l ^ e ∣ q + 1 := by
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have hs2 := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega))
    nlinarith
  rw [hfactor] at hd
  by_cases hm : l ∣ q - 1
  · have hp : ¬ l ∣ q + 1 := by
      intro hh
      have htwo := Nat.dvd_sub hh hm
      have he : q + 1 - (q - 1) = 2 := by omega
      rw [he] at htwo
      exact hl2 ((Nat.prime_dvd_prime_iff_eq hl (by decide : Nat.Prime 2)).mp htwo)
    exact Or.inl (hl.prime.pow_dvd_of_dvd_mul_right e hp hd)
  · exact Or.inr (hl.prime.pow_dvd_of_dvd_mul_left e hm hd)

/-- Odd cross-characteristic contributions in linear dimension two are bounded
by q+1. The characteristic exclusion is expressed directly as nondivisibility. -/
theorem linear_two_odd_cross_contribution_le {q l : ℕ}
    (hx : Admissible (.linear 2 q)) (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear 2 q)).factorization l ≤ q + 1 := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hNpos := lie_order_pos hx (by trivial)
  have hdivN : l ^ (order (.linear 2 q)).factorization l ∣ order (.linear 2 q) :=
    (hl.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  have hdivnum : order (.linear 2 q) ∣ q * (q ^ 2 - 1) := by
    have hd := Nat.div_dvd_of_dvd (denominator_dvd_numerator hx)
    simpa [order, numerator, fieldSize, characteristicExponent, residual, denominator] using hd
  have hdivres : l ^ (order (.linear 2 q)).factorization l ∣ q ^ 2 - 1 :=
    hl.prime.pow_dvd_of_dvd_mul_left _ hlq (hdivN.trans hdivnum)
  rcases odd_prime_power_dvd_adjacent hl hl2 hq hdivres with hm | hp
  · have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hm
    omega
  · exact Nat.le_of_dvd (by omega : 0 < q + 1) hp

/-- For odd field size, every odd cross-characteristic contribution is already
strictly below the characteristic contribution q of linear dimension two.
The separate two-adic branch is not asserted here. -/
theorem linear_two_odd_field_odd_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.linear 2 q)) (hqodd : Odd q)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlq : ¬ l ∣ q) :
    l ^ (order (.linear 2 q)).factorization l < q := by
  let e := (order (.linear 2 q)).factorization l
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hle : l ^ e ≤ q + 1 := linear_two_odd_cross_contribution_le hx hl hl2 hlq
  have hodd : Odd (l ^ e) := (hl.odd_of_ne_two hl2).pow
  have hmodP := Nat.odd_iff.mp hodd
  have hmodQ := Nat.odd_iff.mp hqodd
  have hleq : l ^ e ≤ q := by omega
  have hne : l ^ e ≠ q := by
    intro he
    by_cases he0 : e = 0
    · simp only [he0, pow_zero] at he
      omega
    · have hdiv : l ∣ l ^ e := dvd_pow_self l he0
      rw [he] at hdiv
      exact hlq hdiv
  change l ^ e < q
  omega

end Atlas.OrderArithmetic
