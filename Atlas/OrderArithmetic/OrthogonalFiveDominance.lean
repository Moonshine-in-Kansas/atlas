import Atlas.OrderArithmetic.LinearFourDominance
import Atlas.OrderArithmetic.HighRankDOrthogonal

namespace Atlas.OrderArithmetic

private theorem five_segment_identity (q : ℕ) :
    (∏ i ∈ Finset.Icc 1 4, (q ^ (2 * i) - 1)) =
      (q ^ 2 - 1) * residual (.linear 4 (q ^ 2)) := by
  norm_num [residual, Finset.prod_Icc_succ_top, ← pow_mul]
  ring

/-- The rank-five orthogonal residual bound needs no central cancellation. -/
theorem orthogonal_five_residual_bound {q l A : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q)
    (hA : 0 < A) (hAb : A ≤ q ^ 6) :
    l ^ (A * ∏ i ∈ Finset.Icc 1 4, (q ^ (2 * i) - 1)).factorization l < q ^ 20 := by
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have hR : residual (.linear 4 (q ^ 2)) ≠ 0 := by
    change (∏ i ∈ Finset.Icc 2 4, ((q ^ 2) ^ i - 1)) ≠ 0
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hi2 := (Finset.mem_Icc.mp hi).1
    have hb := Nat.pow_le_pow_right (by omega : 0 < q ^ 2) (by omega : 1 ≤ i)
    simp only [pow_one] at hb
    omega
  have hsmall : q ^ 2 - 1 ≠ 0 := by omega
  rw [five_segment_identity, Nat.factorization_mul hA.ne' (mul_ne_zero hsmall hR),
    Nat.factorization_mul hsmall hR, Finsupp.add_apply, Finsupp.add_apply, pow_add, pow_add]
  have ha := Nat.le_of_dvd hA ((hl.pow_dvd_iff_le_factorization hA.ne').mpr le_rfl)
  have hb := Nat.le_of_dvd (by omega : 0 < q ^ 2 - 1)
    ((hl.pow_dvd_iff_le_factorization hsmall).mpr le_rfl)
  have hc := linear_four_residual_cross_contribution_lt hq2 hl
    (fun hd => hlq (hl.dvd_of_dvd_pow hd))
  have hc' : l ^ (residual (.linear 4 (q ^ 2))).factorization l < q ^ 12 := by
    simpa only [← pow_mul] using hc
  calc
    _ ≤ q ^ 6 * ((q ^ 2 - 1) * l ^ (residual (.linear 4 (q ^ 2))).factorization l) :=
      Nat.mul_le_mul (ha.trans hAb) (Nat.mul_le_mul_right _ hb)
    _ < q ^ 6 * (q ^ 2 * q ^ 12) := by
      apply Nat.mul_lt_mul_of_pos_left _ (pow_pos (by omega) _)
      exact Nat.mul_lt_mul_of_le_of_lt (by omega) hc' (by omega)
    _ = q ^ 20 := by ring

private theorem extra_five_bound {q : ℕ} (hq : 2 ≤ q) : q ^ 5 + 1 ≤ q ^ 6 := by
  have hpos : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.mul_le_mul_left (q ^ 5) hq
  rw [show q ^ 6 = q ^ 5 * q by ring]
  omega

theorem split_orthogonal_five_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.Dplus 5 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dplus 5 q)).factorization l < q ^ 20 := by
  have hq := primePower_two_le hx.2
  have hp : q ≤ q ^ 5 := by simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 1 ≤ 5)
  exact (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq
    (residual_pos hx (by trivial)).ne' (dvd_refl _)).trans_lt
    (orthogonal_five_residual_bound hq hl hlq (by omega : 0 < q ^ 5 - 1)
      (le_trans (by omega : q ^ 5 - 1 ≤ q ^ 5 + 1) (extra_five_bound hq)))

theorem minus_orthogonal_five_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.Dminus 5 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dminus 5 q)).factorization l < q ^ 20 := by
  have hq := primePower_two_le hx.2
  exact (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq
    (residual_pos hx (by trivial)).ne' (dvd_refl _)).trans_lt
    (orthogonal_five_residual_bound hq hl hlq (by omega : 0 < q ^ 5 + 1) (extra_five_bound hq))

end Atlas.OrderArithmetic
