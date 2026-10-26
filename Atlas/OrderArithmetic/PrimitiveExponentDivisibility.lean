import Atlas.OrderArithmetic.PrimitiveDivisorBounds
import Mathlib.FieldTheory.Finite.Basic

namespace Atlas.OrderArithmetic

/-- The primitive index is exactly the multiplicative order of the residue. -/
theorem primitiveDivisor_orderOf {p h l : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) :
    orderOf (p : ZMod l) = h := by
  have hi : ∀ j : ℕ, (p : ZMod l) ^ j = 1 ↔ l ∣ p ^ j - 1 := by
    intro j
    rw [← ZMod.natCast_eq_zero_iff (p ^ j - 1) l,
      Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 1 ≤ p)),
      Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  apply (orderOf_eq_iff hp.1).mpr
  refine ⟨(hi h).mpr hp.2.2.1, ?_⟩
  intro j hj hjpos he
  exact hp.2.2.2 j hjpos hj ((hi j).mp he)

/-- Exact exponent divisibility, including exponent zero. -/
theorem primitiveDivisor_dvd_minus_iff {p h l j : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) :
    l ∣ p ^ j - 1 ↔ h ∣ j := by
  rw [← primitiveDivisor_orderOf hp hpbase, orderOf_dvd_iff_pow_eq_one]
  rw [← ZMod.natCast_eq_zero_iff (p ^ j - 1) l,
    Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 1 ≤ p)),
    Nat.cast_pow, Nat.cast_one, sub_eq_zero]

/-- A primitive index divides one less than its prime divisor. -/
theorem primitiveDivisor_index_dvd_prime_sub_one {p h l : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) : h ∣ l - 1 := by
  letI : Fact l.Prime := ⟨hp.2.1⟩
  have hn : (p : ZMod l) ≠ 0 := by
    intro hz
    exact primitiveDivisor_not_dvd_base hp hpbase ((ZMod.natCast_eq_zero_iff p l).mp hz)
  rw [← primitiveDivisor_orderOf hp hpbase]
  exact ZMod.orderOf_dvd_card_sub_one hn

/-- In particular, a primitive prime is strictly larger than its index. -/
theorem primitiveDivisor_index_lt_prime {p h l : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) : h < l := by
  have hl := hp.2.1.two_le
  have hh := Nat.le_of_dvd (by omega : 0 < l - 1)
    (primitiveDivisor_index_dvd_prime_sub_one hp hpbase)
  omega

/-- A plus factor has twice its exponent divisible by the primitive index. -/
theorem primitiveDivisor_dvd_twice_plus_exponent {p h l j : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p)
    (hd : l ∣ p ^ j + 1) : h ∣ 2 * j := by
  have hu : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
  have hu2 : 1 ≤ (p ^ j) ^ 2 := Nat.one_le_pow _ _ hu
  have hs := Nat.sub_add_cancel hu
  have hs2 := Nat.sub_add_cancel hu2
  have he : (p ^ j) ^ 2 - 1 = (p ^ j - 1) * (p ^ j + 1) := by nlinarith
  apply (primitiveDivisor_dvd_minus_iff hp hpbase).mp
  rw [Nat.mul_comm 2 j, pow_mul, he]
  exact dvd_mul_of_dvd_right hd _

/-- Above primitive index one, a plus exponent itself is not divisible by the index. -/
theorem primitiveDivisor_not_dvd_plus_exponent {p h l j : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) (hh : 1 < h)
    (hd : l ∣ p ^ j + 1) : ¬ h ∣ j := by
  intro hj
  have hm := (primitiveDivisor_dvd_minus_iff hp hpbase).mpr hj
  have ht := Nat.dvd_sub hd hm
  have hu : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
  have he : (p ^ j + 1) - (p ^ j - 1) = 2 := by omega
  rw [he] at ht
  have hl := Nat.le_of_dvd (by decide : 0 < 2) ht
  have hlarge := primitiveDivisor_index_lt_prime hp hpbase
  omega

/-- The quotient of twice a plus exponent by its primitive index is odd. -/
theorem primitiveDivisor_plus_quotient_odd {p h l j : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) (hh : 1 < h)
    (hd : l ∣ p ^ j + 1) : Odd ((2 * j) / h) := by
  have hdiv := primitiveDivisor_dvd_twice_plus_exponent hp hpbase hd
  have he : h * ((2 * j) / h) = 2 * j := Nat.mul_div_cancel' hdiv
  have hn := primitiveDivisor_not_dvd_plus_exponent hp hpbase hh hd
  have ht : ((2 * j) / h) % 2 = 1 := by
    have hmod := Nat.mod_lt ((2 * j) / h) (by decide : 0 < 2)
    by_contra hne
    have hm : ((2 * j) / h) % 2 = 0 := by omega
    have hdecomp := Nat.mod_add_div ((2 * j) / h) 2
    have hj : j = h * (((2 * j) / h) / 2) := by nlinarith
    exact hn ⟨((2 * j) / h) / 2, hj⟩
  refine ⟨((2 * j) / h) / 2, ?_⟩
  have hdecomp := Nat.mod_add_div ((2 * j) / h) 2
  omega

/-- A proper primitive index in a plus factor is at most one third of twice
its exponent. This is the numerical gap needed below the largest index. -/
theorem primitiveDivisor_proper_plus_index_bound {p h l j : ℕ}
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) (hh : 1 < h)
    (hd : l ∣ p ^ j + 1) (hlt : h < 2 * j) : 3 * h ≤ 2 * j := by
  obtain ⟨k, hk⟩ := primitiveDivisor_plus_quotient_odd hp hpbase hh hd
  have he : h * ((2 * j) / h) = 2 * j := Nat.mul_div_cancel'
    (primitiveDivisor_dvd_twice_plus_exponent hp hpbase hd)
  have hpos := hp.1
  have hkpos : 1 ≤ k := by nlinarith
  nlinarith

end Atlas.OrderArithmetic
