import Atlas.OrderArithmetic.FactorialValuation
import Mathlib.NumberTheory.Multiplicity

namespace Atlas.OrderArithmetic

/-- Odd-prime LTE for a block of exponents divisible by a fixed support index. -/
theorem odd_prime_minus_multiple_valuation {l q e j : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (he : 1 ≤ e) (hj : 1 ≤ j)
    (hdiv : l ∣ q ^ e - 1) :
    (q ^ (e * j) - 1).factorization l =
      (q ^ e - 1).factorization l + j.factorization l := by
  letI : Fact l.Prime := ⟨hl⟩
  have hqe : 1 < q ^ e := by
    have hh : q ≤ q ^ e := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < q) he
    omega
  have hnot : ¬ l ∣ q ^ e := by
    intro hd
    have hone := Nat.dvd_sub hd hdiv
    have hs : q ^ e - (q ^ e - 1) = 1 := by omega
    exact hl.not_dvd_one (hs ▸ hone)
  have hh := padicValNat.pow_sub_pow (p := l) (hl.odd_of_ne_two hl2)
    (x := q ^ e) (y := 1) hqe hdiv hnot (n := j) (by omega)
  simpa only [one_pow, ← pow_mul, Nat.factorization_def _ hl] using hh

private theorem minus_block_ne_zero {q e : ℕ} (hq : 2 ≤ q) (he : 1 ≤ e) (t : ℕ) :
    (∏ j ∈ Finset.range t, (q ^ (e * (j + 1)) - 1)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hpow : q ≤ q ^ (e * (j + 1)) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q)
      (by nlinarith : 1 ≤ e * (j + 1))
  omega

/-- Exact accumulated valuation of the supported factors. The factorial term
records all repeated divisibility beyond the initial support factor. -/
theorem odd_prime_minus_block_valuation {l q e : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (he : 1 ≤ e)
    (hdiv : l ∣ q ^ e - 1) (t : ℕ) :
    (∏ j ∈ Finset.range t, (q ^ (e * (j + 1)) - 1)).factorization l =
      t * (q ^ e - 1).factorization l + t.factorial.factorization l := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hpow : q ≤ q ^ (e * (t + 1)) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < q)
        (by nlinarith : 1 ≤ e * (t + 1))
    rw [Finset.prod_range_succ,
      Nat.factorization_mul (minus_block_ne_zero hq he t) (by omega),
      Finsupp.add_apply, ih,
      odd_prime_minus_multiple_valuation hl hl2 hq he (by omega) hdiv,
      Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero t),
      Finsupp.add_apply]
    ring

/-- An accumulated odd-prime contribution is controlled by the initial factor
and the factorial estimate; this bound is uniform in the field and rank. -/
theorem odd_prime_minus_block_contribution_le {l q e : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (he : 1 ≤ e)
    (hdiv : l ∣ q ^ e - 1) (t : ℕ) :
    l ^ (∏ j ∈ Finset.range t, (q ^ (e * (j + 1)) - 1)).factorization l ≤
      (q ^ e - 1) ^ t * 2 ^ t := by
  have hqe : q ≤ q ^ e := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) he
  have hd : l ^ (q ^ e - 1).factorization l ∣ q ^ e - 1 :=
    (hl.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  have hbase := Nat.le_of_dvd (by omega : 0 < q ^ e - 1) hd
  rw [odd_prime_minus_block_valuation hl hl2 hq he hdiv, pow_add]
  have hh : l ^ (t * (q ^ e - 1).factorization l) =
      (l ^ (q ^ e - 1).factorization l) ^ t := by rw [← pow_mul, Nat.mul_comm]
  rw [hh]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hbase t)
    (factorial_prime_contribution_le hl t)

/-- A coarse polynomial-in-q bound for a complete supported block. Applying
this to a family still requires identifying its supported factors. -/
theorem odd_prime_minus_block_contribution_le_field_power {l q e : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (he : 1 ≤ e)
    (hdiv : l ∣ q ^ e - 1) (t : ℕ) :
    l ^ (∏ j ∈ Finset.range t, (q ^ (e * (j + 1)) - 1)).factorization l ≤
      q ^ ((e + 1) * t) := by
  calc
    _ ≤ (q ^ e - 1) ^ t * 2 ^ t :=
      odd_prime_minus_block_contribution_le hl hl2 hq he hdiv t
    _ ≤ (q ^ e) ^ t * q ^ t :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le _ _) t)
        (Nat.pow_le_pow_left hq t)
    _ = q ^ ((e + 1) * t) := by rw [← pow_mul, ← pow_add]; congr 1; ring

end Atlas.OrderArithmetic
