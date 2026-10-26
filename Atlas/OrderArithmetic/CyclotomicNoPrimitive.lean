import Atlas.OrderArithmetic.CyclotomicOddValuation
import Atlas.OrderArithmetic.CyclotomicTwoValuation
import Atlas.OrderArithmetic.CyclotomicSize

namespace Atlas.OrderArithmetic
open Polynomial

/-- Every prime factor of a cyclotomic value which divides the index occurs
with valuation exactly one, once the index exceeds two. -/
theorem cyclotomic_bad_prime_factorization_one {a n l : ℕ}
    (ha : 2 ≤ a) (hn : 2 < n) (hl : l.Prime) (hln : l ∣ n)
    (hdiv : l ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs) :
    (((cyclotomic n ℤ).eval (a : ℤ)).natAbs).factorization l = 1 := by
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) l hl.ne_one
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    simp [hm0] at hnm
    omega
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp only [hk0, pow_zero, one_mul] at hnm
    exact hm (hnm ▸ hln)
  have hdiv' : l ∣ ((cyclotomic (l ^ k * m) ℤ).eval (a : ℤ)).natAbs := by
    simpa only [← hnm] using hdiv
  by_cases hl2 : l = 2
  · subst l
    have hmone : m = 1 := by
      have hd := (cyclotomic_prime_power_index_order (by decide : Nat.Prime 2) hm hdiv').2
      exact Nat.dvd_one.mp (by simpa using hd)
    subst m
    simp only [mul_one] at hnm hdiv'
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      simp only [hk1, pow_one] at hnm
      omega
    have hvalue := cyclotomic_two_power_eval_natAbs (a := a) hk
    have hnot : ¬ 2 ∣ a := by
      intro hda
      rw [hvalue] at hdiv'
      exact prime_not_dvd_pow_add_one (by decide : Nat.Prime 2) hda
        (Nat.one_le_pow _ _ (by decide)) hdiv'
    have hodd : Odd a := by
      apply Nat.odd_iff.mpr
      have hmod := Nat.mod_lt a (by decide : 0 < 2)
      have hmod0 : a % 2 ≠ 0 := fun h => hnot (Nat.dvd_of_mod_eq_zero h)
      omega
    rw [hnm]
    exact cyclotomic_two_power_factorization_two hodd hk2
  · have hodd := hl.odd_of_ne_two hl2
    cases k with
    | zero => omega
    | succ k =>
      rw [hnm]
      exact cyclotomic_odd_prime_power_index_factorization ha hl hodd hmpos hm hdiv'

/-- With no primitive divisor, the whole cyclotomic value is one prime factor
of its index, rather than a larger power of that prime. -/
theorem cyclotomic_value_prime_of_no_primitive {a n : ℕ}
    (ha : 2 ≤ a) (hn : 2 < n) (hno : ¬ ∃ l : ℕ, PrimitiveDivisor a n l) :
    ∃ l : ℕ, l.Prime ∧ l ∣ n ∧ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs = l := by
  let C := ((cyclotomic n ℤ).eval (a : ℤ)).natAbs
  have hCgt : 1 < C := by
    have hbound : (a - 1) ^ n.totient < C :=
      sub_one_pow_totient_lt_natAbs_cyclotomic_eval (n := n) (q := a) (by omega) (by omega)
    have hpow : 1 ≤ (a - 1) ^ n.totient := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨l, hl, hlC⟩ := Nat.exists_prime_and_dvd (by omega : C ≠ 1)
  have hln := cyclotomic_nonprimitive_prime_factor_dvd_index ha (by omega) hl hlC
    (fun h => hno ⟨l, h⟩)
  have hv : C.factorization l = 1 := cyclotomic_bad_prime_factorization_one ha hn hl hln hlC
  refine ⟨l, hl, hln, ?_⟩
  change C = l
  apply Nat.eq_of_factorization_eq (by omega : C ≠ 0) hl.ne_zero
  intro r
  by_cases hrl : r = l
  · subst r
    rw [hv, hl.factorization_self]
  by_cases hr : r.Prime
  · have hnC : ¬ r ∣ C := by
      intro hrC
      exact hrl (cyclotomic_prime_factors_eq_of_no_primitive ha (by omega) hno hr hl hrC hlC)
    have hnl : ¬ r ∣ l := by
      intro hrd
      exact hrl ((Nat.prime_dvd_prime_iff_eq hr hl).mp hrd)
    rw [Nat.factorization_eq_zero_of_not_dvd hnC, Nat.factorization_eq_zero_of_not_dvd hnl]
  · rw [Nat.factorization_eq_zero_of_not_prime C hr, Nat.factorization_eq_zero_of_not_prime l hr]

/-- Primitive divisors exist at every index greater than two for every integer
base at least three. The separate binary exceptional case is not covered here. -/
theorem primitiveDivisor_exists_of_base_ge_three {a n : ℕ}
    (ha : 3 ≤ a) (hn : 2 < n) : ∃ l : ℕ, PrimitiveDivisor a n l := by
  by_contra hno
  obtain ⟨l, hl, hln, he⟩ := cyclotomic_value_prime_of_no_primitive (by omega) hn hno
  have hlt := index_prime_lt_cyclotomic_value ha (by omega) hl hln
  omega

end Atlas.OrderArithmetic
