import Atlas.OrderArithmetic.Positivity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

namespace Atlas.OrderArithmetic
open scoped BigOperators

private theorem power_gt_one {q j : ℕ} (hq : 2 ≤ q) (hj : 1 ≤ j) : 1 < q ^ j :=
  lt_of_lt_of_le (by omega : 1 < q) (Nat.le_pow (by omega))

private theorem minus_lt {q j k : ℕ} (hq : 2 ≤ q) (hj : 1 ≤ j) (hjk : j ≤ k) :
    q ^ j - 1 < q ^ k :=
  (Nat.sub_lt (by have := power_gt_one hq hj; omega) (by omega)).trans_le
    (Nat.pow_le_pow_right (by omega) hjk)

private theorem plus_lt {q j k : ℕ} (hq : 2 ≤ q) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
    q ^ j + 1 < q ^ k := by
  have hp := power_gt_one hq hj
  have hlt : q ^ j + 1 < q ^ (j + 1) := by rw [pow_succ]; nlinarith
  exact hlt.trans_le (Nat.pow_le_pow_right (by omega) hjk)

private theorem mul_lt_power {q A B a b : ℕ} (hq : 2 ≤ q)
    (ha : A < q ^ a) (hb : B < q ^ b) : A * B < q ^ (a + b) := by
  calc
    A * B ≤ A * q ^ b := Nat.mul_le_mul_left _ hb.le
    _ < q ^ a * q ^ b := Nat.mul_lt_mul_of_pos_right ha (pow_pos (by omega) _)
    _ = q ^ (a + b) := (pow_add _ _ _).symm

private theorem prod_lt_power {q : ℕ} (s : Finset ℕ) (v e : ℕ → ℕ)
    (hs : s.Nonempty) (hv : ∀ i ∈ s, 0 < v i) (hb : ∀ i ∈ s, v i < q ^ e i) :
    ∏ i ∈ s, v i < q ^ (∑ i ∈ s, e i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_lt_prod_of_nonempty hv hb hs

private theorem sum_predecessors {d : ℕ} (hd : 2 ≤ d) :
    ∑ i ∈ Finset.Icc 2 d, (i - 1) = d * (d - 1) / 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have hlen : d + 1 - 2 = d - 1 := by omega
  simp only [hlen]
  calc
    ∑ i ∈ Finset.range (d - 1), (2 + i - 1) =
        ∑ i ∈ Finset.range (d - 1), (i + 1) := by
      apply Finset.sum_congr rfl
      intro i _; congr 1 <;> omega
    _ = ∑ i ∈ Finset.range d, i := by
      conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ d), Finset.sum_range_succ']
      simp
    _ = _ := Finset.sum_range_id d

private theorem linear_residual_bound {d q : ℕ} (hd : 2 ≤ d) (hq : 2 ≤ q) :
    residual (.linear d q) < q ^ (2 * (d * (d - 1) / 2)) := by
  have h := prod_lt_power (Finset.Icc 2 d) (fun i => q ^ i - 1) (fun i => 2 * (i - 1))
    ⟨2, by simp [hd]⟩
    (fun i hi => by have := power_gt_one (j := i) hq (by have := (Finset.mem_Icc.mp hi).1; omega); omega)
    (fun i hi => minus_lt hq (by have := (Finset.mem_Icc.mp hi).1; omega)
      (by have := (Finset.mem_Icc.mp hi).1; omega))
  simpa [← Finset.mul_sum, sum_predecessors hd, residual] using h

private theorem unitary_residual_bound {d q : ℕ} (hd : 3 ≤ d) (hq : 2 ≤ q) :
    residual (.unitary d q) < q ^ (2 * (d * (d - 1) / 2)) := by
  have h := prod_lt_power (Finset.Icc 2 d) (unitaryFactor q) (fun i => 2 * (i - 1))
    ⟨2, by simp; omega⟩
    (fun i hi => by
      have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.mp hi).1; omega
      unfold unitaryFactor; split
      · have := power_gt_one hq hi1; omega
      · omega)
    (fun i hi => by
      have hi2 := (Finset.mem_Icc.mp hi).1
      unfold unitaryFactor; split
      · exact minus_lt hq (by omega) (by omega)
      · have hi3 : 3 ≤ i := by
          have : ¬ Even i := by assumption
          have : i ≠ 2 := by intro he; subst i; norm_num at *
          omega
        exact plus_lt hq (by omega) (by omega))
  simpa [← Finset.mul_sum, sum_predecessors (by omega : 2 ≤ d), residual] using h

private theorem even_product_bound {r q : ℕ} (hr : 1 ≤ r) (hq : 2 ≤ q) :
    (∏ i ∈ Finset.Icc 1 r, (q ^ (2 * i) - 1)) < q ^ (r * (2 * r)) := by
  have h := prod_lt_power (Finset.Icc 1 r) (fun i => q ^ (2 * i) - 1) (fun _ => 2 * r)
    ⟨1, by simp [hr]⟩
    (fun i hi => by have := power_gt_one (j := 2 * i) hq (by have := (Finset.mem_Icc.mp hi).1; omega); omega)
    (fun i hi => minus_lt hq (by have := (Finset.mem_Icc.mp hi).1; omega)
      (by have := (Finset.mem_Icc.mp hi).2; omega))
  simpa using h

/-- Classical residual products admit a uniform bound by q^(2a). -/
theorem classical_residual_bound {x : RawEntry} (hx : Admissible x)
    (hc : ∃ r q, x = .linear r q ∨ x = .unitary r q ∨ x = .B r q ∨ x = .C r q ∨
      x = .Dplus r q ∨ x = .Dminus r q) :
    residual x < fieldSize x ^ (2 * characteristicExponent x) := by
  obtain ⟨r, q, rfl | rfl | rfl | rfl | rfl | rfl⟩ := hc
  · exact linear_residual_bound hx.1 (primePower_two_le hx.2.1)
  · exact unitary_residual_bound hx.1 (primePower_two_le hx.2.1)
  · have h := even_product_bound (r := r) (by have := hx.1; omega) (primePower_two_le hx.2.1)
    simpa [residual, fieldSize, characteristicExponent, pow_two, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using h
  · have h := even_product_bound (r := r) (by have := hx.1; omega) (primePower_two_le hx.2.1)
    simpa [residual, fieldSize, characteristicExponent, pow_two, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using h
  · have hq := primePower_two_le hx.2
    have hr : 4 ≤ r := hx.1
    have hprod := even_product_bound (by omega : 1 ≤ r - 1) hq
    have hf := minus_lt hq (by omega : 1 ≤ r) (by omega : r ≤ 2 * (r - 1))
    have h := mul_lt_power hq hf hprod
    change (q ^ r - 1) * _ < q ^ (2 * (r * (r - 1)))
    convert h using 1
    congr 1
    have := Nat.sub_add_cancel (by omega : 1 ≤ r)
    nlinarith
  · have hq := primePower_two_le hx.2
    have hr : 4 ≤ r := hx.1
    have hprod := even_product_bound (by omega : 1 ≤ r - 1) hq
    have hf := plus_lt hq (by omega : 1 ≤ r) (by omega : r + 1 ≤ 2 * (r - 1))
    have h := mul_lt_power hq hf hprod
    change (q ^ r + 1) * _ < q ^ (2 * (r * (r - 1)))
    convert h using 1
    congr 1
    have := Nat.sub_add_cancel (by omega : 1 ≤ r)
    nlinarith

/-- A residual bound gives the exact growth exponent used by the finite reduction. -/
theorem order_growth_of_residual {x : RawEntry} (hx : Admissible x) (hl : IsLie x)
    (hr : residual x < fieldSize x ^ (2 * characteristicExponent x)) :
    order x < fieldSize x ^ (3 * characteristicExponent x) := by
  have hq := primePower_two_le (lie_field_primePower hx hl)
  rw [lie_order_eq hl]
  apply (Nat.div_le_self _ _).trans_lt
  unfold numerator
  have h := Nat.mul_lt_mul_of_pos_left hr
    (pow_pos (by omega : 0 < fieldSize x) (characteristicExponent x))
  calc
    fieldSize x ^ characteristicExponent x * residual x <
        fieldSize x ^ characteristicExponent x * fieldSize x ^ (2 * characteristicExponent x) := h
    _ = fieldSize x ^ (3 * characteristicExponent x) := by
      rw [← pow_add]
      congr 1
      omega

private theorem fixed_product_bound {q k : ℕ} (s : Finset ℕ) (hq : 2 ≤ q)
    (hs : s.Nonempty) (hi : ∀ i ∈ s, 1 ≤ i) (hk : ∑ i ∈ s, i ≤ k) :
    (∏ i ∈ s, (q ^ i - 1)) < q ^ k := by
  have h := prod_lt_power s (fun i => q ^ i - 1) id hs
    (fun i hmem => by have := power_gt_one hq (hi i hmem); omega)
    (fun i hmem => minus_lt hq (hi i hmem) le_rfl)
  exact h.trans_le (Nat.pow_le_pow_right (by omega) hk)

/-- Uniform residual bound, including every exceptional and twisted formula. -/
theorem residual_growth_bound {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    residual x < fieldSize x ^ (2 * characteristicExponent x) := by
  have hq := primePower_two_le (lie_field_primePower hx hl)
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear r q | unitary r q | B r q | C r q | Dplus r q | Dminus r q =>
    apply classical_residual_bound hx
    exact ⟨r, q, by simp⟩
  | F4 q | E6 q | E7 q | E8 q =>
    apply fixed_product_bound _ hq (by simp)
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      omega
    · norm_num [characteristicExponent]
  | G2 q =>
    have h := mul_lt_power hq
      (minus_lt hq (show 1 ≤ 6 by omega) le_rfl)
      (minus_lt hq (show 1 ≤ 2 by omega) le_rfl)
    exact h.trans_le (Nat.pow_le_pow_right (by omega) (by norm_num [characteristicExponent]))
  | twistedE6 q =>
    have h := mul_lt_power hq
      (mul_lt_power hq
        (mul_lt_power hq
          (mul_lt_power hq
            (mul_lt_power hq
              (minus_lt hq (show 1 ≤ 12 by omega) le_rfl)
              (plus_lt (k := 10) hq (show 1 ≤ 9 by omega) (by omega)))
            (minus_lt hq (show 1 ≤ 8 by omega) le_rfl))
          (minus_lt hq (show 1 ≤ 6 by omega) le_rfl))
        (plus_lt (k := 6) hq (show 1 ≤ 5 by omega) (by omega)))
      (minus_lt hq (show 1 ≤ 2 by omega) le_rfl)
    exact h.trans_le (Nat.pow_le_pow_right (by omega) (by norm_num [characteristicExponent]))
  | trialityD4 q =>
    change 2 ≤ q at hq
    have h4 := power_gt_one (j := 4) hq (by omega)
    have hq2 : 4 ≤ q ^ 2 := by nlinarith
    have hp8 : q ^ 8 = (q ^ 4) ^ 2 := by ring
    have hp10 : q ^ 10 = q ^ 8 * q ^ 2 := by ring
    have ht : q ^ 8 + q ^ 4 + 1 < q ^ 10 := by nlinarith
    have h := mul_lt_power hq
      (mul_lt_power hq ht (minus_lt hq (show 1 ≤ 6 by omega) le_rfl))
      (minus_lt hq (show 1 ≤ 2 by omega) le_rfl)
    exact h.trans_le (Nat.pow_le_pow_right (by omega) (by norm_num [characteristicExponent]))
  | suzuki q =>
    have h := mul_lt_power hq
      (plus_lt (k := 3) hq (show 1 ≤ 2 by omega) (by omega))
      (minus_lt hq (show 1 ≤ 1 by omega) le_rfl)
    simpa [fieldSize, residual, characteristicExponent] using h
  | smallRee q =>
    have h := mul_lt_power hq
      (plus_lt (k := 4) hq (show 1 ≤ 3 by omega) (by omega))
      (minus_lt hq (show 1 ≤ 1 by omega) le_rfl)
    have h' := h.trans_le (Nat.pow_le_pow_right (by omega) (show 4 + 1 ≤ 6 by omega))
    simpa [fieldSize, residual, characteristicExponent] using h'
  | largeRee q =>
    have h := mul_lt_power hq
      (mul_lt_power hq
        (mul_lt_power hq
          (plus_lt (k := 7) hq (show 1 ≤ 6 by omega) (by omega))
          (minus_lt hq (show 1 ≤ 4 by omega) le_rfl))
        (plus_lt (k := 4) hq (show 1 ≤ 3 by omega) (by omega)))
      (minus_lt hq (show 1 ≤ 1 by omega) le_rfl)
    have h' := h.trans_le
      (Nat.pow_le_pow_right (by omega) (show 7 + 4 + 4 + 1 ≤ 24 by omega))
    simpa [fieldSize, residual, characteristicExponent] using h'

/-- The coarse uniform growth bound for all unbounded ordinary families. -/
theorem order_growth {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    order x < fieldSize x ^ (3 * characteristicExponent x) :=
  order_growth_of_residual hx hl (residual_growth_bound hx hl)

end Atlas.OrderArithmetic
