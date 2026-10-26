import Atlas.OrderArithmetic.RankOneTwoAdic
import Atlas.OrderArithmetic.CyclotomicNoPrimitive
import Atlas.OrderArithmetic.PrimitiveExponentDivisibility

namespace Atlas.OrderArithmetic

/-- An odd prime power one greater than a positive power of two is either
prime, or is the single exceptional square 9 = 8+1. -/
theorem odd_prime_power_eq_two_power_add_one {l e f : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (he : 1 ≤ e) (hf : 1 ≤ f)
    (heq : l ^ e = 2 ^ f + 1) :
    e = 1 ∨ (l = 3 ∧ e = 2 ∧ f = 3) := by
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have he2 : e ≤ 2 := by
    by_contra hh
    obtain ⟨r, hr⟩ := primitiveDivisor_exists_of_base_ge_three (n := e) hl3 (by omega)
    have hd : r ∣ 2 ^ f := by simpa [heq] using hr.2.2.1
    have hr2 : r = 2 := Nat.prime_eq_prime_of_dvd_pow hr.2.1 Nat.prime_two hd
    have hlt := primitiveDivisor_index_lt_prime hr (by omega)
    omega
  by_cases he1 : e = 1
  · exact Or.inl he1
  have hee : e = 2 := by omega
  subst e
  have hprod : (l - 1) * (l + 1) = 2 ^ f := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ l)
    nlinarith [heq]
  have hm : l - 1 ∣ 2 ^ f := by
    rw [← hprod]
    exact dvd_mul_right _ _
  have hp : l + 1 ∣ 2 ^ f := by
    rw [← hprod]
    exact dvd_mul_left _ _
  obtain ⟨a, ha, hma⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm
  obtain ⟨b, hb, hpb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hp
  have hlval := odd_adjacent_two_valuation_one (by omega : 2 ≤ l)
    (hl.odd_of_ne_two hl2)
  have hlthree : l = 3 := by
    rcases hlval with hv | hv
    · rw [hma, Nat.factorization_pow_self Nat.prime_two] at hv
      have : l - 1 = 2 := by simpa [hv] using hma
      omega
    · rw [hpb, Nat.factorization_pow_self Nat.prime_two] at hv
      have : l + 1 = 2 := by simpa [hv] using hpb
      omega
  have hfthree : f = 3 := by
    have hh : (2 : ℕ) ^ f = 2 ^ 3 := by rw [hlthree] at heq; norm_num at heq ⊢; omega
    exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hh
  exact Or.inr ⟨hlthree, rfl, hfthree⟩

/-- A cross-prime contribution at least as large as the characteristic part
for binary-field L₂ forces a Fermat-prime neighbor or q=8. -/
theorem linear_two_even_cross_large_forces_fermat_or_eight {q l f : ℕ}
    (hx : Admissible (.linear 2 q)) (hf : 1 ≤ f) (hq : q = 2 ^ f)
    (hl : l.Prime) (hlq : ¬ l ∣ q)
    (hlarge : q ≤ l ^ (order (.linear 2 q)).factorization l) :
    (q + 1).Prime ∨ q = 8 := by
  have hq2 : 2 ≤ q := primePower_two_le hx.2.1
  have hqeven : Even q := by
    rw [hq]
    exact (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
  have hl2 : l ≠ 2 := by
    intro hh
    apply hlq
    rw [hh, hq]
    exact dvd_pow_self 2 (by omega)
  let e := (order (.linear 2 q)).factorization l
  have hle : l ^ e ≤ q + 1 := linear_two_odd_cross_contribution_le hx hl hl2 hlq
  have hpo := Nat.odd_iff.mp ((hl.odd_of_ne_two hl2).pow (n := e))
  have hqe := Nat.even_iff.mp hqeven
  have heq : l ^ e = q + 1 := by change q ≤ l ^ e at hlarge; omega
  have he : 1 ≤ e := by
    by_contra hh
    have : e = 0 := by omega
    simp only [this, pow_zero] at heq
    omega
  rcases odd_prime_power_eq_two_power_add_one hl hl2 he hf
      (by simpa [hq] using heq) with he1 | ⟨hl3, he2, hf3⟩
  · left
    have hh : l = q + 1 := by simpa [he1] using heq
    exact hh ▸ hl
  · right
    simp [hq, hf3]

/-- Outside the Fermat-prime neighbor and the binary cubic exception, every
cross-prime contribution in binary-field L₂ is below q. -/
theorem linear_two_even_cross_contribution_lt {q l f : ℕ}
    (hx : Admissible (.linear 2 q)) (hf : 1 ≤ f) (hq : q = 2 ^ f)
    (hl : l.Prime) (hlq : ¬ l ∣ q) (hnprime : ¬ (q + 1).Prime) (hq8 : q ≠ 8) :
    l ^ (order (.linear 2 q)).factorization l < q := by
  by_contra hh
  rcases linear_two_even_cross_large_forces_fermat_or_eight hx hf hq hl hlq
      (by omega) with hp | h8
  · exact hnprime hp
  · exact hq8 h8

end Atlas.OrderArithmetic
