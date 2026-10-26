import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal
import Atlas.OrderArithmetic.RankOneTwoAdic
import Mathlib.Tactic.Zify

namespace Atlas.OrderArithmetic

def unitaryThreeCyclotomic (q : ℕ) : ℕ := q * (q - 1) + 1

theorem unitaryThreeCyclotomic_odd (q : ℕ) : Odd (unitaryThreeCyclotomic q) :=
  (Nat.even_mul_pred_self q).add_odd (by decide : Odd (1 : ℕ))

theorem unitary_three_residual_factor {q : ℕ} (hq : 2 ≤ q) :
    residual (.unitary 3 q) = (q + 1) ^ 2 * (q - 1) * unitaryThreeCyclotomic q := by
  have hs : 1 ≤ q := by omega
  have hs2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hs
  norm_num [residual, unitaryFactor, Finset.prod_Icc_succ_top]
  unfold unitaryThreeCyclotomic
  zify [hs, hs2]
  ring

theorem unitaryThreeCyclotomic_minus_support {q l : ℕ} (hl : l.Prime)
    (hm : l ∣ q - 1) : ¬ l ∣ unitaryThreeCyclotomic q := by
  intro hb
  have hp : l ∣ q * (q - 1) := dvd_mul_of_dvd_right hm q
  have hh := Nat.dvd_sub hb hp
  have he : unitaryThreeCyclotomic q - q * (q - 1) = 1 := by
    unfold unitaryThreeCyclotomic
    omega
  exact hl.not_dvd_one (he ▸ hh)

theorem unitaryThreeCyclotomic_plus_support {q l : ℕ} (hq : 2 ≤ q)
    (hl : l.Prime) (hl3 : l ≠ 3) (hp : l ∣ q + 1) :
    ¬ l ∣ unitaryThreeCyclotomic q := by
  intro hb
  have he : unitaryThreeCyclotomic q = (q + 1) * (q - 2) + 3 := by
    unfold unitaryThreeCyclotomic
    zify [show 1 ≤ q by omega, hq]
    ring
  have hh := Nat.dvd_sub hb (dvd_mul_of_dvd_left hp (q - 2))
  rw [he, Nat.add_sub_cancel_left] at hh
  exact hl3 ((Nat.prime_dvd_prime_iff_eq hl (by decide : Nat.Prime 3)).mp hh)

theorem unitaryThreeCyclotomic_three_valuation_le (q : ℕ) :
    (unitaryThreeCyclotomic q).factorization 3 ≤ 1 := by
  have hpos : unitaryThreeCyclotomic q ≠ 0 := by unfold unitaryThreeCyclotomic; omega
  have hnot : ¬ 9 ∣ unitaryThreeCyclotomic q := by
    intro hh
    have hmod := Nat.mod_eq_zero_of_dvd hh
    have hid : unitaryThreeCyclotomic q + q = q ^ 2 + 1 := by
      unfold unitaryThreeCyclotomic
      cases q with
      | zero => norm_num
      | succ q => simp; ring
    have hcong := congrArg (fun n : ℕ => n % 9) hid
    rw [Nat.add_mod, hmod, zero_add, Nat.mod_mod, Nat.add_mod, Nat.pow_mod] at hcong
    have hr : q % 9 < 9 := Nat.mod_lt _ (by decide)
    interval_cases h : q % 9 <;> norm_num [h] at hcong
  by_contra hh
  have hd : 3 ^ 2 ∣ unitaryThreeCyclotomic q :=
    ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization hpos).mpr (by omega)
  exact hnot (by simpa using hd)

private theorem unitary_three_small_factors {q : ℕ} (hq : 3 ≤ q) :
    (q + 1) ^ 2 < q ^ 3 ∧ q - 1 < q ^ 3 ∧ unitaryThreeCyclotomic q < q ^ 3 := by
  have hs := Nat.sub_add_cancel (by omega : 1 ≤ q)
  have hB : unitaryThreeCyclotomic q ≤ q ^ 2 + 1 := by
    unfold unitaryThreeCyclotomic
    nlinarith
  have hc : 3 * q ^ 2 ≤ q ^ 3 := by nlinarith [Nat.mul_le_mul_right (q ^ 2) hq]
  constructor
  · nlinarith [sq_nonneg (q - 3)]
  constructor <;> nlinarith [sq_nonneg (q - 3)]

/-- The generic odd-prime branch avoids both small shared primes. -/
theorem unitary_three_odd_non_three_contribution_lt {q l : ℕ}
    (hx : Admissible (.unitary 3 q)) (hl : l.Prime) (hl2 : l ≠ 2) (hl3 : l ≠ 3)
    (hlq : ¬ l ∣ q) : l ^ (order (.unitary 3 q)).factorization l < q ^ 3 := by
  have hq2 : 2 ≤ q := primePower_two_le hx.2.1
  have hq : 3 ≤ q := by have := hx.2.2; omega
  have hd := cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq
  rw [unitary_three_residual_factor hq2] at hd
  obtain ⟨hpluslt, hminuslt, hBlt⟩ := unitary_three_small_factors hq
  by_cases hb : l ∣ unitaryThreeCyclotomic q
  · have hp : ¬ l ∣ q + 1 := fun hh => unitaryThreeCyclotomic_plus_support hq2 hl hl3 hh hb
    have hm : ¬ l ∣ q - 1 := fun hh => unitaryThreeCyclotomic_minus_support hl hh hb
    have hn : ¬ l ∣ (q + 1) ^ 2 * (q - 1) := by
      intro hh
      rcases hl.dvd_mul.mp hh with hh | hh
      · exact hp (hl.dvd_of_dvd_pow hh)
      · exact hm hh
    have hh := hl.prime.pow_dvd_of_dvd_mul_left _ hn hd
    exact (Nat.le_of_dvd (by unfold unitaryThreeCyclotomic; omega) hh).trans_lt hBlt
  · have hh := hl.prime.pow_dvd_of_dvd_mul_right _ hb hd
    by_cases hm : l ∣ q - 1
    · have hp : ¬ l ∣ q + 1 := by
        intro hp
        have hd2 := Nat.dvd_sub hp hm
        have he : q + 1 - (q - 1) = 2 := by omega
        rw [he] at hd2
        exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd2)
      have hdminus := hl.prime.pow_dvd_of_dvd_mul_left _
        (fun h => hp (hl.dvd_of_dvd_pow h)) hh
      exact (Nat.le_of_dvd (by omega) hdminus).trans_lt hminuslt
    · have hdplus := hl.prime.pow_dvd_of_dvd_mul_right _ hm hh
      exact (Nat.le_of_dvd (by positivity) hdplus).trans_lt hpluslt

private theorem prime_contribution_mul_le {l A B : ℕ} (hl : l.Prime)
    (hA : 0 < A) (hB : 0 < B) :
    l ^ (A * B).factorization l ≤ A * l ^ B.factorization l := by
  have hd : l ^ A.factorization l ∣ A :=
    (hl.pow_dvd_iff_le_factorization hA.ne').mpr le_rfl
  rw [Nat.factorization_mul hA.ne' hB.ne', Finsupp.add_apply, pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hA hd)

/-- The possible shared cyclotomic prime contributes at most three copies
of the squared adjacent factor; central cancellation is not needed. -/
theorem unitary_three_three_contribution_le {q : ℕ}
    (hx : Admissible (.unitary 3 q)) (h3q : ¬ 3 ∣ q) :
    3 ^ (order (.unitary 3 q)).factorization 3 ≤ 3 * (q + 1) ^ 2 := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hl : Nat.Prime 3 := by decide
  have hd := cross_prime_order_contribution_dvd_residual hx (by trivial) hl h3q
  rw [unitary_three_residual_factor hq] at hd
  have hBpos : 0 < unitaryThreeCyclotomic q := by unfold unitaryThreeCyclotomic; omega
  by_cases hm : 3 ∣ q - 1
  · have hp : ¬ 3 ∣ q + 1 := by
      intro hh
      have hd2 := Nat.dvd_sub hh hm
      have he : q + 1 - (q - 1) = 2 := by omega
      rw [he] at hd2
      norm_num at hd2
    have hb := unitaryThreeCyclotomic_minus_support hl hm
    have hd' := hl.prime.pow_dvd_of_dvd_mul_right _ hb hd
    have hd'' := hl.prime.pow_dvd_of_dvd_mul_left _
      (fun hh => hp (hl.dvd_of_dvd_pow hh)) hd'
    have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd''
    have hs := Nat.sub_le q 1
    nlinarith
  · have he : (q + 1) ^ 2 * (q - 1) * unitaryThreeCyclotomic q =
        ((q + 1) ^ 2 * unitaryThreeCyclotomic q) * (q - 1) := by ring
    rw [he] at hd
    have hd' := hl.prime.pow_dvd_of_dvd_mul_right _ hm hd
    have hv := (hl.pow_dvd_iff_le_factorization
      (mul_ne_zero (by positivity) hBpos.ne')).mp hd'
    have hb := (Nat.pow_le_pow_right hl.pos hv).trans
      (prime_contribution_mul_le hl (by positivity : 0 < (q + 1) ^ 2) hBpos)
    have h3 : 3 ^ (unitaryThreeCyclotomic q).factorization 3 ≤ 3 := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ))
        (unitaryThreeCyclotomic_three_valuation_le q)
    exact hb.trans (by nlinarith)

theorem unitary_three_two_contribution_bound {q : ℕ}
    (hx : Admissible (.unitary 3 q)) (ho : Odd q) :
    2 ^ (order (.unitary 3 q)).factorization 2 ≤ 2 * (q + 1) ^ 2 ∨
      2 ^ (order (.unitary 3 q)).factorization 2 ≤ 4 * (q - 1) := by
  have hq : 2 ≤ q := primePower_two_le hx.2.1
  have hnq : ¬ 2 ∣ q := by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    have := Nat.odd_iff.mp ho
    omega
  have hnB : ¬ 2 ∣ unitaryThreeCyclotomic q := by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    have := Nat.odd_iff.mp (unitaryThreeCyclotomic_odd q)
    omega
  have hd := cross_prime_order_contribution_dvd_residual hx (by trivial) Nat.prime_two hnq
  rw [unitary_three_residual_factor hq] at hd
  have hd' := Nat.prime_two.prime.pow_dvd_of_dvd_mul_right _ hnB hd
  have hv := (Nat.prime_two.pow_dvd_iff_le_factorization
    (mul_ne_zero (by positivity : (q + 1) ^ 2 ≠ 0) (by omega : q - 1 ≠ 0))).mp hd'
  have hfac : ((q + 1) ^ 2 * (q - 1)).factorization 2 =
      2 * (q + 1).factorization 2 + (q - 1).factorization 2 := by
    rw [Nat.factorization_mul (by positivity) (by omega), Nat.factorization_pow]
    simp
  rw [hfac] at hv
  have hb := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hv
  have hpe : 2 ^ (2 * (q + 1).factorization 2 + (q - 1).factorization 2) =
      (2 ^ (q + 1).factorization 2) ^ 2 * 2 ^ (q - 1).factorization 2 := by
    rw [pow_add, ← pow_mul]
    congr 1
    congr 1
    omega
  rw [hpe] at hb
  have hp : 2 ^ (q + 1).factorization 2 ≤ q + 1 := Nat.le_of_dvd (by omega)
    ((Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl)
  have hm : 2 ^ (q - 1).factorization 2 ≤ q - 1 := Nat.le_of_dvd (by omega)
    ((Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl)
  rcases odd_adjacent_two_valuation_one hq ho with hminus | hplus
  · left
    rw [hminus] at hb
    norm_num at hb
    have hs := Nat.pow_le_pow_left hp 2
    nlinarith
  · right
    rw [hplus] at hb
    norm_num at hb
    nlinarith

/-- Full cross-prime dominance for U3, with the exact exceptional field q=3
explicitly removed. The inadmissible binary case is already excluded by hx. -/
theorem unitary_three_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.unitary 3 q)) (hq3 : q ≠ 3)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.unitary 3 q)).factorization l < q ^ 3 := by
  have hq2 : 2 ≤ q := primePower_two_le hx.2.1
  have hq : 4 ≤ q := by have := hx.2.2; omega
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hc : 4 * q ^ 2 ≤ q ^ 3 := by nlinarith [Nat.mul_le_mul_right (q ^ 2) hq]
    have hs := Nat.sub_le q 1
    rcases unitary_three_two_contribution_bound hx ho with hh | hh <;> nlinarith
  · by_cases hl3 : l = 3
    · subst l
      by_cases hq4 : q = 4
      · subst q
        have hd := cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq
        have hr : residual (.unitary 3 4) = 975 := by
          norm_num [residual, unitaryFactor, Finset.prod_Icc_succ_top]
        rw [hr] at hd
        change 3 ^ (order (.unitary 3 4)).factorization 3 ∣ 325 * 3 at hd
        have hh := hl.prime.pow_dvd_of_dvd_mul_left _ (by decide : ¬ 3 ∣ 325) hd
        have hle := Nat.le_of_dvd (by decide : 0 < (3 : ℕ)) hh
        norm_num
        omega
      · have hq5 : 5 ≤ q := by omega
        have hc : 5 * q ^ 2 ≤ q ^ 3 := by nlinarith [Nat.mul_le_mul_right (q ^ 2) hq5]
        have hh := unitary_three_three_contribution_le hx hlq
        nlinarith
    · exact unitary_three_odd_non_three_contribution_lt hx hl hl2 hl3 hlq

end Atlas.OrderArithmetic
