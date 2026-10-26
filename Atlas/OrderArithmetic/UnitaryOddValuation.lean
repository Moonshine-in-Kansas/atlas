import Atlas.OrderArithmetic.ValuationSupport

namespace Atlas.OrderArithmetic

/-- The parity-defined unitary factor is the absolute value of a single
signed-base power difference. -/
theorem unitaryFactor_eq_signed_natAbs {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    unitaryFactor q i = ((-(q : ℤ)) ^ i - 1).natAbs := by
  unfold unitaryFactor
  split_ifs with hi
  · rw [hi.neg_pow]
    have he : ((q ^ i - 1 : ℕ) : ℤ) = (q : ℤ) ^ i - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
    rw [← he, Int.natAbs_natCast]
  · have ho := Nat.not_even_iff_odd.mp hi
    rw [ho.neg_pow]
    have he : -(q : ℤ) ^ i - 1 = -((q : ℤ) ^ i + 1) := by ring
    rw [he, Int.natAbs_neg]
    have hc : ((q ^ i + 1 : ℕ) : ℤ) = (q : ℤ) ^ i + 1 := by norm_cast
    rw [← hc, Int.natAbs_natCast]

theorem unitaryFactor_pos_of_two_le {q i : ℕ} (hq : 2 ≤ q) (hi : 1 ≤ i) :
    0 < unitaryFactor q i := by
  have hp : q ≤ q ^ i := by simpa using Nat.pow_le_pow_right (by omega : 0 < q) hi
  unfold unitaryFactor
  split <;> omega

theorem unitaryFactor_prime_dvd_iff_signed {q l i : ℕ} (hq : 2 ≤ q) :
    l ∣ unitaryFactor q i ↔ (l : ℤ) ∣ (-(q : ℤ)) ^ i - 1 := by
  rw [unitaryFactor_eq_signed_natAbs hq]
  simpa only [Int.natAbs_natCast] using
    (Int.natAbs_dvd_natAbs (a := (l : ℤ)) (b := (-(q : ℤ)) ^ i - 1))

/-- Odd-prime LTE on the signed base handles both parities uniformly. -/
theorem unitary_odd_prime_multiple_valuation {l q e j : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (hlq : ¬ l ∣ q)
    (he : 1 ≤ e) (hj : 1 ≤ j) (hdiv : l ∣ unitaryFactor q e) :
    (unitaryFactor q (e * j)).factorization l =
      (unitaryFactor q e).factorization l + j.factorization l := by
  letI : Fact l.Prime := ⟨hl⟩
  have hxy := (unitaryFactor_prime_dvd_iff_signed hq).mp hdiv
  have hnot : ¬ (l : ℤ) ∣ (-(q : ℤ)) ^ e := by
    intro hh
    have hd := (Nat.prime_iff_prime_int.mp hl).dvd_of_dvd_pow hh
    have hdq : (l : ℤ) ∣ (q : ℤ) := by simpa using hd
    exact hlq (by exact_mod_cast hdq)
  have hLTE := Int.emultiplicity_pow_sub_pow hl (hl.odd_of_ne_two hl2) hxy hnot j
  simp only [one_pow, ← pow_mul] at hLTE
  rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl, Nat.factorization_def _ hl,
    ← Nat.cast_inj (R := ℕ∞), Nat.cast_add,
    padicValNat_eq_emultiplicity (unitaryFactor_pos_of_two_le hq (by nlinarith)).ne',
    padicValNat_eq_emultiplicity (unitaryFactor_pos_of_two_le hq he).ne',
    padicValNat_eq_emultiplicity (by omega : j ≠ 0),
    unitaryFactor_eq_signed_natAbs hq, unitaryFactor_eq_signed_natAbs hq,
    Int.emultiplicity_natAbs, Int.emultiplicity_natAbs]
  exact hLTE

theorem unitary_odd_prime_block_valuation {l q e : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (hlq : ¬ l ∣ q)
    (he : 1 ≤ e) (hdiv : l ∣ unitaryFactor q e) (t : ℕ) :
    (∏ j ∈ Finset.range t, unitaryFactor q (e * (j + 1))).factorization l =
      t * (unitaryFactor q e).factorization l + t.factorial.factorization l := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hprod : (∏ j ∈ Finset.range t, unitaryFactor q (e * (j + 1))) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact (unitaryFactor_pos_of_two_le hq (by nlinarith : 1 ≤ e * (j + 1))).ne'
    rw [Finset.prod_range_succ, Nat.factorization_mul hprod
      (unitaryFactor_pos_of_two_le hq (by nlinarith : 1 ≤ e * (t + 1))).ne',
      Finsupp.add_apply, ih, unitary_odd_prime_multiple_valuation hl hl2 hq hlq he (by omega) hdiv,
      Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero t),
      Finsupp.add_apply]
    ring

theorem unitary_odd_prime_block_contribution_le {l q e : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (hlq : ¬ l ∣ q)
    (he : 1 ≤ e) (hdiv : l ∣ unitaryFactor q e) (t : ℕ) :
    l ^ (∏ j ∈ Finset.range t, unitaryFactor q (e * (j + 1))).factorization l ≤
      (unitaryFactor q e) ^ t * 2 ^ t := by
  have hA := unitaryFactor_pos_of_two_le hq he
  have hb : l ^ (unitaryFactor q e).factorization l ≤ unitaryFactor q e :=
    Nat.le_of_dvd hA ((hl.pow_dvd_iff_le_factorization hA.ne').mpr le_rfl)
  rw [unitary_odd_prime_block_valuation hl hl2 hq hlq he hdiv, pow_add]
  have hp : l ^ (t * (unitaryFactor q e).factorization l) =
      (l ^ (unitaryFactor q e).factorization l) ^ t := by rw [← pow_mul, Nat.mul_comm]
  rw [hp]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hb t) (factorial_prime_contribution_le hl t)

/-- Multiplicative order of the signed residue is the exact unitary support. -/
theorem unitaryFactor_dvd_iff_signed_order {q l i : ℕ} (hq : 2 ≤ q) :
    l ∣ unitaryFactor q i ↔ orderOf (-(q : ZMod l)) ∣ i := by
  rw [unitaryFactor_prime_dvd_iff_signed hq, orderOf_dvd_iff_pow_eq_one,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_neg, Int.cast_natCast, Int.cast_one, sub_eq_zero]

theorem unitary_odd_prime_segment_valuation {l q e : ℕ}
    (hl : l.Prime) (hl2 : l ≠ 2) (hq : 2 ≤ q) (hlq : ¬ l ∣ q)
    (he : 1 ≤ e) (hsupport : ∀ i : ℕ, l ∣ unitaryFactor q i ↔ e ∣ i) (d : ℕ) :
    (∏ i ∈ Finset.Icc 1 d, unitaryFactor q i).factorization l =
      (d / e) * (unitaryFactor q e).factorization l + (d / e).factorial.factorization l := by
  have hnonzero : ∀ i ∈ Finset.Icc 1 d, unitaryFactor q i ≠ 0 := by
    intro i hi
    exact (unitaryFactor_pos_of_two_le hq (Finset.mem_Icc.mp hi).1).ne'
  have hblock : ∀ j ∈ Finset.range (d / e), unitaryFactor q (e * (j + 1)) ≠ 0 := by
    intro j hj
    exact (unitaryFactor_pos_of_two_le hq (by nlinarith : 1 ≤ e * (j + 1))).ne'
  have hdiv := (hsupport e).mpr (dvd_refl e)
  rw [Nat.factorization_prod_apply hnonzero,
    sum_Icc_supported_on_multiples he (fun i => (unitaryFactor q i).factorization l)]
  · rw [← Nat.factorization_prod_apply hblock]
    exact unitary_odd_prime_block_valuation hl hl2 hq hlq he hdiv (d / e)
  · intro i hi hn
    exact Nat.factorization_eq_zero_of_not_dvd (fun hh => hn ((hsupport i).mp hh))

end Atlas.OrderArithmetic
