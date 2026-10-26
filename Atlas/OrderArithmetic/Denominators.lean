import Atlas.OrderArithmetic.Orders
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith

namespace Atlas.OrderArithmetic
open scoped BigOperators

theorem lie_field_primePower {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    PrimePower (fieldSize x) := by
  cases x <;> simp_all only [Admissible, IsLie, fieldSize]
  all_goals obtain ⟨m, hm, rfl⟩ := hx
  all_goals first
    | exact ⟨2, 2 * m + 1, by norm_num, by omega, rfl⟩
    | exact ⟨3, 2 * m + 1, by norm_num, by omega, rfl⟩

theorem denominator_pos {x : RawEntry} (hx : Admissible x) : 0 < denominator x := by
  cases x <;> simp only [denominator]
  all_goals try exact Nat.zero_lt_one
  all_goals apply Nat.gcd_pos_of_pos_left
  all_goals try norm_num
  all_goals have := hx.1; omega

private theorem add_one_dvd_square_sub_one {q : ℕ} (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 := by
  refine ⟨q - 1, ?_⟩
  have := Nat.sub_add_cancel hq
  have hsq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have := Nat.sub_add_cancel hsq
  nlinarith

private theorem square_factor_linear {q d : ℕ} (hd : 2 ≤ d) :
    q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 d, (q ^ i - 1) :=
  Finset.dvd_prod_of_mem _ (by simp [hd])

private theorem square_factor_even {q r : ℕ} (hr : 1 ≤ r) :
    q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 1 r, (q ^ (2 * i) - 1) := by
  simpa using Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1)
    (show 1 ∈ Finset.Icc 1 r by simp [hr])

/-- Every central divisor divides the noncharacteristic part already. -/
theorem denominator_dvd_residual {x : RawEntry} (hx : Admissible x) :
    denominator x ∣ residual x := by
  cases x with
  | linear d q =>
    exact (Nat.gcd_dvd_right d (q - 1)).trans
      ((Nat.sub_one_dvd_pow_sub_one q 2).trans (square_factor_linear hx.1))
  | unitary d q =>
    have hq := primePower_two_le hx.2.1
    have hdiv := (Nat.gcd_dvd_right d (q + 1)).trans
      (add_one_dvd_square_sub_one (by omega : 1 ≤ q))
    have hf : unitaryFactor q 2 = q ^ 2 - 1 := by simp [unitaryFactor]
    exact hdiv.trans (hf ▸ Finset.dvd_prod_of_mem (unitaryFactor q)
      (show 2 ∈ Finset.Icc 2 d by have := hx.1; simp; omega))
  | B r q | C r q =>
    exact (Nat.gcd_dvd_right 2 (q - 1)).trans
      ((Nat.sub_one_dvd_pow_sub_one q 2).trans (square_factor_even (by have := hx.1; omega)))
  | Dplus r q => exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right 4 _) _
  | Dminus r q => exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right 4 _) _
  | E6 q =>
    exact (Nat.gcd_dvd_right 3 (q - 1)).trans ((Nat.sub_one_dvd_pow_sub_one q 2).trans
      (Finset.dvd_prod_of_mem _ (show 2 ∈ ({2, 5, 6, 8, 9, 12} : Finset ℕ) by simp)))
  | E7 q =>
    exact (Nat.gcd_dvd_right 2 (q - 1)).trans ((Nat.sub_one_dvd_pow_sub_one q 2).trans
      (Finset.dvd_prod_of_mem _ (show 2 ∈ ({2, 6, 8, 10, 12, 14, 18} : Finset ℕ) by simp)))
  | twistedE6 q =>
    have hq := primePower_two_le hx
    exact dvd_mul_of_dvd_right ((Nat.gcd_dvd_right 3 (q + 1)).trans
      (add_one_dvd_square_sub_one (by omega))) _
  | _ => exact one_dvd _

theorem denominator_dvd_numerator {x : RawEntry} (hx : Admissible x) :
    denominator x ∣ numerator x := dvd_mul_of_dvd_right (denominator_dvd_residual hx) _

private theorem gcd_four_dvd_square {q t : ℕ} (ht : Even q → Odd t) :
    Nat.gcd 4 t ∣ q ^ 2 - 1 := by
  by_cases he : Even q
  · have hg : Nat.gcd 4 t = 1 := by
      simpa using ((ht he).coprime_two_left.pow_left 2).gcd_eq_one
    rw [hg]
    exact one_dvd _
  · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp he
    apply (Nat.gcd_dvd_left 4 t).trans
    refine ⟨k * (k + 1), ?_⟩
    have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have := Nat.sub_add_cancel hq
    nlinarith [sq_nonneg (q : ℤ)]

/-- Central division can only remove primes already present in q²−1. -/
theorem denominator_dvd_square_sub_one {x : RawEntry} (hx : Admissible x)
    (hl : IsLie x) : denominator x ∣ fieldSize x ^ 2 - 1 := by
  have hq := primePower_two_le (lie_field_primePower hx hl)
  cases x with
  | linear d q | B d q | C d q | E6 q | E7 q =>
    exact (Nat.gcd_dvd_right _ (q - 1)).trans (Nat.sub_one_dvd_pow_sub_one q 2)
  | unitary d q | twistedE6 q =>
    simp only [fieldSize] at hq
    exact (Nat.gcd_dvd_right _ (q + 1)).trans (add_one_dvd_square_sub_one (by omega))
  | Dplus r q =>
    change Nat.gcd 4 (q ^ r - 1) ∣ q ^ 2 - 1
    simp only [fieldSize] at hq
    apply gcd_four_dvd_square
    intro he
    have hev := Nat.even_iff.mp (he.pow_of_ne_zero (show r ≠ 0 by have := hx.1; omega))
    have hpos : 1 ≤ q ^ r := Nat.one_le_pow _ _ (by omega)
    exact Nat.odd_iff.mpr (by omega)
  | Dminus r q =>
    change Nat.gcd 4 (q ^ r + 1) ∣ q ^ 2 - 1
    simp only [fieldSize] at hq
    apply gcd_four_dvd_square
    intro he
    have hev := Nat.even_iff.mp (he.pow_of_ne_zero (show r ≠ 0 by have := hx.1; omega))
    exact Nat.odd_iff.mpr (by omega)
  | _ => exact one_dvd _

end Atlas.OrderArithmetic

