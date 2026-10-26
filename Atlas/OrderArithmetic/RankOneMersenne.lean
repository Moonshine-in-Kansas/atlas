import Atlas.OrderArithmetic.RankOneTwoAdic
import Mathlib.NumberTheory.Multiplicity

namespace Atlas.OrderArithmetic

/-- An odd base greater than one cannot have a nontrivial power immediately
below a power of two. This elementary statement needs no primality assumption. -/
theorem odd_power_successor_power_two_exponent {a f k : ℕ}
    (ha : 3 ≤ a) (hao : Odd a) (hf : 1 ≤ f) (he : a ^ f + 1 = 2 ^ k) :
    f = 1 := by
  have hapow : a ≤ a ^ f := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < a) hf
  have hk : 2 ≤ k := by
    by_contra hh
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl <;> norm_num at he <;> omega
  have hfo : Odd f := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨t, ht⟩
    have hodd : Odd (a ^ t) := hao.pow
    have hm := Nat.odd_iff.mp hodd
    have hm4 : a ^ t % 4 = 1 ∨ a ^ t % 4 = 3 := by omega
    have hs : a ^ f % 4 = 1 := by
      rw [ht, pow_add, Nat.mul_mod]
      rcases hm4 with hm4 | hm4 <;> rw [hm4] <;> norm_num
    have hd : 4 ∣ 2 ^ k := by
      simpa using (pow_dvd_pow (2 : ℕ) hk)
    have hz := Nat.mod_eq_zero_of_dvd hd
    rw [← he, Nat.add_mod, hs] at hz
    norm_num at hz
  have hp : Prime (2 : ℤ) := by norm_num
  have ha2 : ¬ (2 : ℕ) ∣ a := by
    intro hd
    have hm := Nat.odd_iff.mp hao
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hf2 : ¬ (2 : ℕ) ∣ f := by
    intro hd
    have hm := Nat.odd_iff.mp hfo
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hsum : (2 : ℤ) ∣ (a : ℤ) - (-1) := by
    have hd : 2 ∣ a + 1 := Nat.dvd_of_mod_eq_zero (by
      have hm := Nat.odd_iff.mp hao
      omega)
    have hdZ : (2 : ℤ) ∣ (a : ℤ) + 1 := by exact_mod_cast hd
    simpa only [sub_neg_eq_add] using hdZ
  have hna : ¬ (2 : ℤ) ∣ (a : ℤ) := by exact_mod_cast ha2
  have hnf : ¬ (2 : ℤ) ∣ (f : ℤ) := by exact_mod_cast hf2
  have hgeom := not_dvd_geom_sum₂ hp hsum hna hnf
  have hid := geom_sum₂_mul (a : ℤ) (-1) f
  rw [hfo.neg_one_pow] at hid
  have heZ : (a : ℤ) ^ f + 1 = (2 : ℤ) ^ k := by exact_mod_cast he
  have hdprod : (2 : ℤ) ^ k ∣
      (∑ i ∈ Finset.range f, (a : ℤ) ^ i * (-1 : ℤ) ^ (f - 1 - i)) *
        ((a : ℤ) - (-1)) := by
    rw [hid]
    simpa using heZ.symm.dvd
  have hdZ := hp.pow_dvd_of_dvd_mul_left k hgeom hdprod
  have hdZ' : (2 : ℤ) ^ k ∣ (a : ℤ) + 1 := by
    simpa only [sub_neg_eq_add] using hdZ
  have hdN : 2 ^ k ∣ a + 1 := by exact_mod_cast hdZ'
  have hle := Nat.le_of_dvd (by omega : 0 < a + 1) hdN
  have hpowle : a ^ f ≤ a ^ 1 := by simpa only [pow_one] using (by omega : a ^ f ≤ a)
  have hfle := (Nat.pow_le_pow_iff_right (by omega : 1 < a)).mp hpowle
  omega

/-- In particular a Mersenne prime-power field is already a prime field. -/
theorem odd_prime_power_successor_power_two {p f k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (he : p ^ f + 1 = 2 ^ k) : f = 1 :=
  odd_power_successor_power_two_exponent (by have := hp.two_le; omega)
    (hp.odd_of_ne_two hp2) hf he

/-- The sole possible failure of strict cross-characteristic dominance for
odd-field linear dimension two has Mersenne prime field size. -/
theorem linear_two_odd_cross_large_forces_mersenne_prime {q l : ℕ}
    (hx : Admissible (.linear 2 q)) (ho : Odd q)
    (hl : l.Prime) (hlq : ¬ l ∣ q)
    (hlarge : q ≤ l ^ (order (.linear 2 q)).factorization l) :
    l = 2 ∧ q.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q + 1 = 2 ^ k := by
  have hl2 : l = 2 := by
    by_contra hh
    have := linear_two_odd_field_odd_cross_contribution_lt hx ho hl hh hlq
    omega
  subst l
  obtain ⟨k, hk, he⟩ := linear_two_odd_two_contribution_ge_forces_power_two
    (primePower_two_le hx.2.1) ho hlarge
  obtain ⟨p, f, hp, hf, hq⟩ := hx.2.1
  have hp2 : p ≠ 2 := by
    intro hh
    have hd : 2 ∣ q := by rw [hq, hh]; exact dvd_pow_self 2 (by omega)
    have hm := Nat.odd_iff.mp ho
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hf1 := odd_prime_power_successor_power_two hp hp2 hf (by simpa [hq] using he)
  have hqp : q = p := by simpa [hf1] using hq
  exact ⟨rfl, by simpa [hqp] using hp, k, hk, he⟩

/-- Away from prime Mersenne field sizes, every cross-prime contribution is
strictly smaller than the characteristic contribution q. -/
theorem linear_two_odd_cross_contribution_lt_of_not_mersenne {q l : ℕ}
    (hx : Admissible (.linear 2 q)) (ho : Odd q)
    (hl : l.Prime) (hlq : ¬ l ∣ q)
    (hnot : ¬ (q.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q + 1 = 2 ^ k)) :
    l ^ (order (.linear 2 q)).factorization l < q := by
  by_contra hh
  exact hnot (linear_two_odd_cross_large_forces_mersenne_prime hx ho hl hlq
    (by omega)).2

end Atlas.OrderArithmetic
