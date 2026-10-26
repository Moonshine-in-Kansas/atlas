import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal

namespace Atlas.OrderArithmetic

private theorem even_segment_cross_contribution_le {q l : ℕ}
    (hq : 2 ≤ q) (hl : l.Prime) (hlq : ¬ l ∣ q) (s : ℕ) :
    l ^ (∏ i ∈ Finset.Icc 1 s, (q ^ (2 * i) - 1)).factorization l ≤ q ^ (4 * s) := by
  by_cases hl2 : l = 2
  · subst l
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun hh => hlq (even_iff_two_dvd.mp hh))
    exact (two_contribution_even_segment_le hq ho s).trans
      (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 3 * s ≤ 4 * s))
  · have hq2 : 2 ≤ q ^ 2 := by nlinarith
    have hb := odd_cross_prime_minus_segment_contribution_le hl hl2 hq2
      (fun hh => hlq (hl.dvd_of_dvd_pow hh)) s
    have hp : (q ^ 2) ^ (2 * s) = q ^ (4 * s) := by
      rw [← pow_mul]; congr 1; omega
    rw [hp] at hb
    simpa only [pow_mul] using hb

/-- A single extra orthogonal factor and a complete even segment have a
uniform cross-prime bound, independent of the central divisor. -/
theorem extra_even_segment_contribution_le {A r q l : ℕ}
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hl : l.Prime) (hlq : ¬ l ∣ q)
    (hA : 0 < A) (hAbound : A ≤ q ^ (r + 1)) :
    l ^ (A * ∏ i ∈ Finset.Icc 1 (r - 1), (q ^ (2 * i) - 1)).factorization l ≤
      q ^ (5 * r - 3) := by
  have hbase : l ^ A.factorization l ≤ A := Nat.le_of_dvd hA
    ((hl.pow_dvd_iff_le_factorization hA.ne').mpr le_rfl)
  rw [Nat.factorization_mul hA.ne' (even_minus_segment_ne_zero hq (r - 1)),
    Finsupp.add_apply, pow_add]
  calc
    _ ≤ q ^ (r + 1) * q ^ (4 * (r - 1)) :=
      Nat.mul_le_mul (hbase.trans hAbound) (even_segment_cross_contribution_le hq hl hlq _)
    _ = q ^ (5 * r - 3) := by rw [← pow_add]; congr 1; omega

private theorem orthogonal_extra_bound {q r : ℕ} (hq : 2 ≤ q) :
    q ^ r + 1 ≤ q ^ (r + 1) := by
  have hp : 1 ≤ q ^ r := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  nlinarith

theorem split_orthogonal_cross_contribution_le {r q l : ℕ}
    (hx : Admissible (.Dplus r q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dplus r q)).factorization l ≤ q ^ (5 * r - 3) := by
  have hq : 2 ≤ q := primePower_two_le hx.2
  have hr : 4 ≤ r := hx.1
  have hp : q ≤ q ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 1 ≤ r)
  have hA : 0 < q ^ r - 1 := by omega
  have hb : q ^ r - 1 ≤ q ^ (r + 1) :=
    (by omega : q ^ r - 1 ≤ q ^ r + 1).trans (orthogonal_extra_bound hq)
  exact (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq
    (residual_pos hx (by trivial)).ne' (dvd_refl _)).trans
      (extra_even_segment_contribution_le hq (by omega) hl hlq hA hb)

theorem minus_orthogonal_cross_contribution_le {r q l : ℕ}
    (hx : Admissible (.Dminus r q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dminus r q)).factorization l ≤ q ^ (5 * r - 3) := by
  have hq : 2 ≤ q := primePower_two_le hx.2
  have hr : 4 ≤ r := hx.1
  exact (cross_prime_contribution_le_of_residual_dvd hx (by trivial) hl hlq
    (residual_pos hx (by trivial)).ne' (dvd_refl _)).trans
      (extra_even_segment_contribution_le hq (by omega) hl hlq (by omega)
        (orthogonal_extra_bound hq))

theorem split_orthogonal_cross_contribution_lt_of_six_le {r q l : ℕ}
    (hx : Admissible (.Dplus r q)) (hr : 6 ≤ r)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dplus r q)).factorization l < q ^ (r * (r - 1)) := by
  have hq : 2 ≤ q := primePower_two_le hx.2
  have he : 5 * r - 3 < r * (r - 1) := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ r)
    have ht := Nat.sub_add_cancel (by omega : 3 ≤ 5 * r)
    nlinarith
  exact (split_orthogonal_cross_contribution_le hx hl hlq).trans_lt
    ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr he)

theorem minus_orthogonal_cross_contribution_lt_of_six_le {r q l : ℕ}
    (hx : Admissible (.Dminus r q)) (hr : 6 ≤ r)
    (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.Dminus r q)).factorization l < q ^ (r * (r - 1)) := by
  have hq : 2 ≤ q := primePower_two_le hx.2
  have he : 5 * r - 3 < r * (r - 1) := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ r)
    have ht := Nat.sub_add_cancel (by omega : 3 ≤ 5 * r)
    nlinarith
  exact (minus_orthogonal_cross_contribution_le hx hl hlq).trans_lt
    ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr he)

end Atlas.OrderArithmetic
