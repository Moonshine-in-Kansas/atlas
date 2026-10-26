import Atlas.OrderArithmetic.CyclotomicPrimeSupport
import Mathlib.NumberTheory.Multiplicity

namespace Atlas.OrderArithmetic
open Polynomial

private theorem natAbs_integer_power_sub_one {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    ((a : ℤ) ^ j - 1).natAbs = a ^ j - 1 := by
  have he : ((a ^ j - 1 : ℕ) : ℤ) = (a : ℤ) ^ j - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ ha), Nat.cast_pow, Nat.cast_one]
  rw [← he, Int.natAbs_natCast]

/-- Evaluated cyclotomic product divisibility retains a proper-divisor factor. -/
theorem cyclotomic_eval_mul_proper_factor_dvd {a d n : ℕ} (ha : 1 ≤ a)
    (hd : d ∈ n.properDivisors) :
    (a ^ d - 1) * ((cyclotomic n ℤ).eval (a : ℤ)).natAbs ∣ a ^ n - 1 := by
  have hpoly := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hd
  have heval := Polynomial.eval_dvd (x := (a : ℤ)) hpoly
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one] at heval
  have habs := Int.natAbs_dvd_natAbs.mpr heval
  simpa only [Int.natAbs_mul, natAbs_integer_power_sub_one ha] using habs

/-- Exact odd-prime valuation in the nonprimitive cyclotomic branch. A single
proper-divisor product divisibility and one LTE step bound the valuation above
by one; the assumed prime divisibility supplies the lower bound. -/
theorem cyclotomic_odd_prime_power_index_factorization
    {a l k m : ℕ} (ha : 2 ≤ a) (hl : l.Prime) (hodd : Odd l)
    (hmpos : 0 < m) (hm : ¬ l ∣ m)
    (hdiv : l ∣ ((cyclotomic (l ^ (k + 1) * m) ℤ).eval (a : ℤ)).natAbs) :
    (((cyclotomic (l ^ (k + 1) * m) ℤ).eval (a : ℤ)).natAbs).factorization l = 1 := by
  letI : Fact l.Prime := ⟨hl⟩
  let d := l ^ k * m
  let n := l ^ (k + 1) * m
  let C := ((cyclotomic n ℤ).eval (a : ℤ)).natAbs
  have hdpos : 0 < d := Nat.mul_pos (pow_pos hl.pos _) hmpos
  have hnd : n = d * l := by dsimp [n, d]; rw [pow_succ]; ring
  have hnpos : 0 < n := by rw [hnd]; exact Nat.mul_pos hdpos hl.pos
  have hdproper : d ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors]
    refine ⟨⟨l, hnd⟩, ?_⟩
    have hp2 := hl.two_le
    rw [hnd]
    nlinarith
  have had : 2 ≤ a ^ d := ha.trans (Nat.le_pow (by omega))
  have han : 2 ≤ a ^ n := ha.trans (Nat.le_pow (by omega))
  have hS0 : a ^ d - 1 ≠ 0 := by omega
  have hN0 : a ^ n - 1 ≠ 0 := by omega
  have hprod : (a ^ d - 1) * C ∣ a ^ n - 1 :=
    cyclotomic_eval_mul_proper_factor_dvd (by omega) hdproper
  have hC0 : C ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod
    exact hN0 (by simpa using hprod)
  have horder : orderOf (a : ZMod l) = m :=
    (cyclotomic_prime_power_index_order hl hm hdiv).1
  have hpow : (a : ZMod l) ^ d = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [horder]
    exact dvd_mul_left m (l ^ k)
  have hsmall : l ∣ a ^ d - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub (by omega : 1 ≤ a ^ d), Nat.cast_pow, Nat.cast_one, hpow, sub_self]
  have hnot : ¬ l ∣ a ^ d := by
    intro hh
    have hone := Nat.dvd_sub hh hsmall
    have he : a ^ d - (a ^ d - 1) = 1 := by omega
    rw [he] at hone
    exact hl.not_dvd_one hone
  have hLTE := padicValNat.pow_sub_pow (p := l) hodd
    (x := a ^ d) (y := 1) (by omega) hsmall hnot (n := l) hl.ne_zero
  simp only [one_pow, padicValNat_self] at hLTE
  have hexp : (a ^ d) ^ l = a ^ n := by rw [← pow_mul, ← hnd]
  rw [hexp] at hLTE
  have hLTEfac : (a ^ n - 1).factorization l = (a ^ d - 1).factorization l + 1 := by
    simpa only [Nat.factorization_def _ hl] using hLTE
  have hfac := (Nat.factorization_le_iff_dvd (mul_ne_zero hS0 hC0) hN0).mpr hprod
  have hv : (a ^ d - 1).factorization l + C.factorization l ≤
      (a ^ n - 1).factorization l := by
    simpa only [Nat.factorization_mul hS0 hC0, Finsupp.add_apply] using hfac l
  have hlow : 1 ≤ C.factorization l := (hl.dvd_iff_one_le_factorization hC0).mp hdiv
  change C.factorization l = 1
  omega

end Atlas.OrderArithmetic
