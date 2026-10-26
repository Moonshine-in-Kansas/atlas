import Atlas.OrderArithmetic.StrictOddSegment
import Atlas.OrderArithmetic.TwoAdicAccumulation

namespace Atlas.OrderArithmetic

/-- A plus factor divides the corresponding doubled minus factor. -/
theorem plus_factor_dvd_even_minus {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    q ^ i + 1 ∣ q ^ (2 * i) - 1 := by
  have hu : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have hu2 : 1 ≤ (q ^ i) ^ 2 := Nat.one_le_pow _ _ hu
  have hs := Nat.sub_add_cancel hu
  have hs2 := Nat.sub_add_cancel hu2
  have he : (q ^ i) ^ 2 - 1 = (q ^ i - 1) * (q ^ i + 1) := by nlinarith
  rw [Nat.mul_comm 2 i, pow_mul, he]
  exact dvd_mul_left _ _

/-- The six twisted E₆ factors occupy six distinct positions in the even
segment through9; the two plus factors use positions5 and9. -/
theorem twistedE6_residual_dvd_even_segment {q : ℕ} (hq : 2 ≤ q) :
    residual (.twistedE6 q) ∣ ∏ i ∈ Finset.Icc 1 9, (q ^ (2 * i) - 1) := by
  have hd : residual (.twistedE6 q) ∣
      (q ^ 12 - 1) * (q ^ 18 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 10 - 1) * (q ^ 2 - 1) := by
    exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
      (mul_dvd_mul (dvd_refl _) (plus_factor_dvd_even_minus (by omega) 9))
      (dvd_refl _)) (dvd_refl _)) (plus_factor_dvd_even_minus (by omega) 5)) (dvd_refl _)
  have he : (q ^ 12 - 1) * (q ^ 18 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 10 - 1) * (q ^ 2 - 1) =
      ∏ i ∈ ({1, 3, 4, 5, 6, 9} : Finset ℕ), (q ^ (2 * i) - 1) := by
    norm_num [Finset.prod_insert]
    ring
  rw [he] at hd
  apply hd.trans
  apply Finset.prod_dvd_prod_of_subset
  decide

/-- Full cross-characteristic dominance for the twisted E₆ literal formula.
The odd-prime argument uses the strict segment bound at base q², while the
binary contribution is already bounded by q²⁷. -/
theorem twistedE6_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.twistedE6 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.twistedE6 q)).factorization l < q ^ 36 := by
  have hq : 2 ≤ q := primePower_two_le hx
  have hdiv := (cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq).trans
    (twistedE6_residual_dvd_even_segment hq)
  have hv := (hl.pow_dvd_iff_le_factorization (even_minus_segment_ne_zero hq 9)).mp hdiv
  have hb := Nat.pow_le_pow_right hl.pos hv
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    have hbound := hb.trans (two_contribution_even_segment_le hq ho 9)
    exact hbound.trans_lt ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide))
  · have hq2 : 2 ≤ q ^ 2 := by nlinarith
    have hn : ¬ l ∣ q ^ 2 := fun hh => hlq (hl.dvd_of_dvd_pow hh)
    have hstrict := odd_cross_prime_minus_segment_contribution_lt hl hl2 hq2 hn (by decide : 1 ≤ 9)
    have he : (q ^ 2) ^ (2 * 9) = q ^ 36 := by rw [← pow_mul]
    rw [he] at hstrict
    apply hb.trans_lt
    simpa only [pow_mul] using hstrict

end Atlas.OrderArithmetic
