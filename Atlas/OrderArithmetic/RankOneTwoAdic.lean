import Atlas.OrderArithmetic.RankOneDominance

namespace Atlas.OrderArithmetic

private theorem two_factorization_one {n : ℕ} (hn : n ≠ 0)
    (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) : n.factorization 2 = 1 := by
  have hp : Nat.Prime 2 := by decide
  have hlo := (hp.dvd_iff_one_le_factorization hn).mp h2
  have hhi : ¬ 2 ≤ n.factorization 2 := by
    intro h
    have hd : 2 ^ 2 ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr h
    exact h4 (by simpa using hd)
  omega

/-- Of the two neighbors of an odd integer, one has two-adic valuation one. -/
theorem odd_adjacent_two_valuation_one {q : ℕ} (hq : 2 ≤ q) (ho : Odd q) :
    (q - 1).factorization 2 = 1 ∨ (q + 1).factorization 2 = 1 := by
  have hmod := Nat.odd_iff.mp ho
  have hm : 2 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hp : 2 ∣ q + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  by_cases hfour : 4 ∣ q - 1
  · right
    apply two_factorization_one (by omega) hp
    intro hh
    have hd := Nat.dvd_sub hh hfour
    have he : q + 1 - (q - 1) = 2 := by omega
    rw [he] at hd
    norm_num at hd
  · exact Or.inl (two_factorization_one (by omega) hm hfour)

/-- Exact two-adic valuation of the odd-field linear degree-two order formula. -/
theorem linear_two_odd_two_valuation {q : ℕ} (hq : 2 ≤ q) (ho : Odd q) :
    (order (.linear 2 q)).factorization 2 =
      (q - 1).factorization 2 + (q + 1).factorization 2 - 1 := by
  have hmod := Nat.odd_iff.mp ho
  have hqm : 2 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hnq : ¬ 2 ∣ q := by
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hg : Nat.gcd 2 (q - 1) = 2 := Nat.gcd_eq_left hqm
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have hs2 := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega))
    nlinarith
  have hd : 2 ∣ q * ((q - 1) * (q + 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hqm _) _
  rw [linear_two_order, hg, hfactor, Nat.factorization_div hd,
    Nat.factorization_mul (by omega : q ≠ 0) (mul_ne_zero (by omega : q - 1 ≠ 0) (by omega)),
    Nat.factorization_mul (by omega : q - 1 ≠ 0) (by omega : q + 1 ≠ 0)]
  simp only [Finsupp.tsub_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnq, zero_add,
    Nat.prime_two.factorization_self]

/-- The actual two-contribution is the two-part of one of the adjacent factors. -/
theorem linear_two_odd_two_contribution_adjacent {q : ℕ} (hq : 2 ≤ q) (ho : Odd q) :
    2 ^ (order (.linear 2 q)).factorization 2 = 2 ^ (q - 1).factorization 2 ∨
    2 ^ (order (.linear 2 q)).factorization 2 = 2 ^ (q + 1).factorization 2 := by
  have hv := linear_two_odd_two_valuation hq ho
  rcases odd_adjacent_two_valuation_one hq ho with hm | hp
  · right
    congr 1
    omega
  · left
    congr 1
    omega

/-- Failure of strict characteristic dominance in the odd-field two-adic
branch forces q+1 to be an exact power of two. -/
theorem linear_two_odd_two_contribution_ge_forces_power_two {q : ℕ}
    (hq : 2 ≤ q) (ho : Odd q) (hlarge : q ≤ 2 ^ (order (.linear 2 q)).factorization 2) :
    ∃ k : ℕ, 1 ≤ k ∧ q + 1 = 2 ^ k := by
  have hp : Nat.Prime 2 := by decide
  rcases linear_two_odd_two_contribution_adjacent hq ho with hm | hplus
  · have hd : 2 ^ (q - 1).factorization 2 ∣ q - 1 :=
      (hp.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
    have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd
    rw [hm] at hlarge
    omega
  · have hd : 2 ^ (q + 1).factorization 2 ∣ q + 1 :=
      (hp.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
    have hle := Nat.le_of_dvd (by omega : 0 < q + 1) hd
    have hmod := Nat.odd_iff.mp ho
    have h2 : 2 ∣ q + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hk : 1 ≤ (q + 1).factorization 2 :=
      (hp.dvd_iff_one_le_factorization (by omega)).mp h2
    have hev : Even (2 ^ (q + 1).factorization 2) :=
      (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
    have hpowmod := Nat.even_iff.mp hev
    rw [hplus] at hlarge
    exact ⟨(q + 1).factorization 2, hk, by omega⟩

end Atlas.OrderArithmetic
