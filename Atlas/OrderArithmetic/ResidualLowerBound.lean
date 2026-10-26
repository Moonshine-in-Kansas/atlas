import Atlas.OrderArithmetic.Positivity

namespace Atlas.OrderArithmetic
open scoped BigOperators

private theorem square_sub_gt {q : ℕ} (hq : 2 ≤ q) : q + 1 ≤ q ^ 2 - 1 := by
  have := Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)
  nlinarith

/-- The noncharacteristic factor survives central division nontrivially. -/
theorem denominator_lt_residual {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    denominator x < residual x := by
  have hq := primePower_two_le (lie_field_primePower hx hl)
  have hr := residual_pos hx hl
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear d q =>
    simp only [fieldSize] at hq
    have hf : q ^ 2 - 1 ∣ residual (.linear d q) :=
      Finset.dvd_prod_of_mem _ (show 2 ∈ Finset.Icc 2 d by simp [hx.1])
    have hb := Nat.le_of_dvd hr hf
    have hg := Nat.gcd_le_right d (show 0 < q - 1 by omega)
    have hs := square_sub_gt hq
    change Nat.gcd d (q - 1) < _
    omega
  | unitary d q =>
    simp only [fieldSize] at hq
    have hf : q ^ 3 + 1 ∣ residual (.unitary d q) := by
      have ht := Finset.dvd_prod_of_mem (unitaryFactor q)
        (show 3 ∈ Finset.Icc 2 d by have := hx.1; simp; omega)
      norm_num [unitaryFactor, residual, Nat.even_iff] at ht ⊢
      exact ht
    have hb := Nat.le_of_dvd hr hf
    have hg := Nat.gcd_le_right d (show 0 < q + 1 by omega)
    have hp := Nat.pow_le_pow_right (show 1 ≤ q by omega) (show 2 ≤ 3 by omega)
    have hs := square_sub_gt hq
    change Nat.gcd d (q + 1) < _
    omega
  | B r q | C r q =>
    simp only [fieldSize] at hq
    have hf : q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 1 r, (q ^ (2 * i) - 1) := by
      simpa using Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1)
        (show 1 ∈ Finset.Icc 1 r by have := hx.1; simp; omega)
    have hb := Nat.le_of_dvd hr hf
    have hg := Nat.gcd_le_left (q - 1) (show 0 < 2 by omega)
    have hs := square_sub_gt hq
    change Nat.gcd 2 (q - 1) < _
    omega
  | Dplus r q | Dminus r q =>
    simp only [fieldSize] at hq
    have hn : 4 ≤ r := hx.1
    have hp : 2 ^ 4 ≤ q ^ r :=
      (Nat.pow_le_pow_left hq 4).trans (Nat.pow_le_pow_right (by omega) hn)
    all_goals first
      | have hb := Nat.le_of_dvd hr (show q ^ r - 1 ∣ residual (.Dplus r q) from dvd_mul_right _ _)
        have hg := Nat.gcd_le_left (q ^ r - 1) (show 0 < 4 by omega)
        change Nat.gcd 4 (q ^ r - 1) < _
        norm_num at hp
        omega
      | have hb := Nat.le_of_dvd hr (show q ^ r + 1 ∣ residual (.Dminus r q) from dvd_mul_right _ _)
        have hg := Nat.gcd_le_left (q ^ r + 1) (show 0 < 4 by omega)
        change Nat.gcd 4 (q ^ r + 1) < _
        norm_num at hp
        omega
  | E6 q | E7 q =>
    simp only [fieldSize] at hq
    have hs := square_sub_gt hq
    all_goals first
      | have hf : q ^ 2 - 1 ∣ residual (.E6 q) := Finset.dvd_prod_of_mem _ (by simp)
        have hb := Nat.le_of_dvd hr hf
        have hg := Nat.gcd_le_right 3 (show 0 < q - 1 by omega)
        change Nat.gcd 3 (q - 1) < _
        omega
      | have hf : q ^ 2 - 1 ∣ residual (.E7 q) := Finset.dvd_prod_of_mem _ (by simp)
        have hb := Nat.le_of_dvd hr hf
        have hg := Nat.gcd_le_right 2 (show 0 < q - 1 by omega)
        change Nat.gcd 2 (q - 1) < _
        omega
  | twistedE6 q =>
    simp only [fieldSize] at hq
    have hf : q ^ 5 + 1 ∣ residual (.twistedE6 q) :=
      dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hb := Nat.le_of_dvd hr hf
    have hg := Nat.gcd_le_right 3 (show 0 < q + 1 by omega)
    have hp := Nat.pow_le_pow_right (show 1 ≤ q by omega) (show 2 ≤ 5 by omega)
    have hs := square_sub_gt hq
    change Nat.gcd 3 (q + 1) < _
    omega
  | G2 q | F4 q | E8 q | trialityD4 q =>
    simp only [fieldSize] at hq
    have hs := square_sub_gt hq
    all_goals first
      | have hf : q ^ 2 - 1 ∣ residual (.G2 q) := dvd_mul_left _ _
        have hb := Nat.le_of_dvd hr hf
        change 1 < _
        omega
      | have hf : q ^ 2 - 1 ∣ residual (.F4 q) := Finset.dvd_prod_of_mem _ (by simp)
        have hb := Nat.le_of_dvd hr hf
        change 1 < _
        omega
      | have hf : q ^ 2 - 1 ∣ residual (.E8 q) := Finset.dvd_prod_of_mem _ (by simp)
        have hb := Nat.le_of_dvd hr hf
        change 1 < _
        omega
      | have hf : q ^ 2 - 1 ∣ residual (.trialityD4 q) := dvd_mul_left _ _
        have hb := Nat.le_of_dvd hr hf
        change 1 < _
        omega
  | suzuki q | smallRee q | largeRee q =>
    simp only [fieldSize] at hq
    all_goals first
      | have hf : q ^ 2 + 1 ∣ residual (.suzuki q) := dvd_mul_right _ _
        have hb := Nat.le_of_dvd hr hf
        have hs := square_sub_gt hq
        change 1 < _
        omega
      | have hf : q ^ 3 + 1 ∣ residual (.smallRee q) := dvd_mul_right _ _
        have hb := Nat.le_of_dvd hr hf
        have hp : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
        change 1 < _
        omega
      | have hf : q ^ 6 + 1 ∣ residual (.largeRee q) :=
          dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
        have hb := Nat.le_of_dvd hr hf
        have hp : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
        change 1 < _
        omega

theorem residual_quotient_gt_one {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    1 < residual x / denominator x := by
  have he := Nat.div_mul_cancel (denominator_dvd_residual hx)
  have hd := denominator_pos hx
  have ht := denominator_lt_residual hx hl
  by_contra h
  have hb : residual x / denominator x ≤ 1 := by omega
  have := Nat.mul_le_mul_right (denominator x) hb
  omega

end Atlas.OrderArithmetic
