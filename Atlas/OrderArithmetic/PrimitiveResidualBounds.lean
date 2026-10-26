import Atlas.OrderArithmetic.PrimitiveDivisorBounds
import Atlas.OrderArithmetic.IndexBounds
import Mathlib.Tactic.SplitIfs

namespace Atlas.OrderArithmetic
open scoped BigOperators

/-- The triality quartic factor embeds into the twelfth minus factor. -/
theorem triality_quartic_dvd_twelfth (q : ℕ) :
    q ^ 8 + q ^ 4 + 1 ∣ q ^ 12 - 1 := by
  refine ⟨q ^ 4 - 1, ?_⟩
  rw [Nat.mul_sub_left_distrib, mul_one]
  have h : (q ^ 8 + q ^ 4 + 1) * q ^ 4 + 1 =
      q ^ 12 + (q ^ 8 + q ^ 4 + 1) := by ring
  omega

/-- Every residual prime lies within the stated largest-index profile. This
uses a supplied primitive divisor and proves no existence theorem for it. -/
theorem primitiveDivisor_not_dvd_residual_of_large_index
    {x : RawEntry} {p f h l : ℕ} (hx : Admissible x) (hl : IsLie x)
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) (hf : 1 ≤ f)
    (hfield : fieldSize x = p ^ f) (hlarge : f * topIndex x < h) :
    ¬ l ∣ residual x := by
  have hminus : ∀ j : ℕ, 1 ≤ j → j ≤ topIndex x →
      ¬ l ∣ fieldSize x ^ j - 1 := by
    intro j hj htop hd
    rw [hfield, ← pow_mul] at hd
    have hb := primitiveDivisor_le_minus_index hp (by nlinarith : 0 < f * j) hd
    have hm := Nat.mul_le_mul_left f htop
    omega
  have hplus : ∀ j : ℕ, 1 ≤ j → 2 * j ≤ topIndex x →
      ¬ l ∣ fieldSize x ^ j + 1 := by
    intro j hj htop hd
    rw [hfield, ← pow_mul] at hd
    have hb := primitiveDivisor_le_plus_index hp hpbase (by nlinarith : 0 < f * j) hd
    have hm := Nat.mul_le_mul_left f htop
    nlinarith
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear d q =>
    apply hp.2.1.prime.not_dvd_finsetProd
    intro i hi
    have hb := Finset.mem_Icc.mp hi
    exact hminus i (by omega) hb.2
  | unitary d q =>
    have hd : 3 ≤ d := hx.1
    apply hp.2.1.prime.not_dvd_finsetProd
    intro i hi
    have hb := Finset.mem_Icc.mp hi
    unfold unitaryFactor
    split_ifs with hei
    · apply hminus i (by omega)
      simp only [topIndex]
      split <;> omega
    · apply hplus i (by omega)
      simp only [topIndex]
      split_ifs with hed
      · have hne : i ≠ d := by intro e; subst i; exact hei hed
        omega
      · omega
  | B r q | C r q =>
    apply hp.2.1.prime.not_dvd_finsetProd
    intro i hi
    have hb := Finset.mem_Icc.mp hi
    exact hminus (2 * i) (by omega) (by simp only [topIndex]; omega)
  | Dplus r q =>
    have hr := hx.1
    apply hp.2.1.prime.not_dvd_mul
    · exact hminus r (by omega) (by simp only [topIndex]; omega)
    · apply hp.2.1.prime.not_dvd_finsetProd
      intro i hi
      have hb := Finset.mem_Icc.mp hi
      exact hminus (2 * i) (by omega) (by simp only [topIndex]; omega)
  | Dminus r q =>
    have hr := hx.1
    apply hp.2.1.prime.not_dvd_mul
    · exact hplus r (by omega) (by simp [topIndex])
    · apply hp.2.1.prime.not_dvd_finsetProd
      intro i hi
      have hb := Finset.mem_Icc.mp hi
      exact hminus (2 * i) (by omega) (by simp only [topIndex]; omega)
  | F4 q | E6 q | E7 q | E8 q =>
    apply hp.2.1.prime.not_dvd_finsetProd
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    exact hminus i (by omega) (by simp only [topIndex]; omega)
  | G2 q =>
    exact hp.2.1.prime.not_dvd_mul (hminus 6 (by omega) (by simp [topIndex]))
      (hminus 2 (by omega) (by simp [topIndex]))
  | twistedE6 q =>
    repeat apply hp.2.1.prime.not_dvd_mul
    all_goals first
      | exact hminus _ (by omega) (by simp [topIndex])
      | exact hplus _ (by omega) (by simp [topIndex])
  | trialityD4 q =>
    apply hp.2.1.prime.not_dvd_mul
    · apply hp.2.1.prime.not_dvd_mul
      · intro hd
        exact hminus 12 (by omega) (by simp [topIndex])
          (hd.trans (triality_quartic_dvd_twelfth q))
      · exact hminus 6 (by omega) (by simp [topIndex])
    · exact hminus 2 (by omega) (by simp [topIndex])
  | suzuki q =>
    exact hp.2.1.prime.not_dvd_mul (hplus 2 (by omega) (by simp [topIndex]))
      (by simpa only [fieldSize, pow_one] using hminus 1 (by omega) (by simp [topIndex]))
  | smallRee q =>
    exact hp.2.1.prime.not_dvd_mul (hplus 3 (by omega) (by simp [topIndex]))
      (by simpa only [fieldSize, pow_one] using hminus 1 (by omega) (by simp [topIndex]))
  | largeRee q =>
    apply hp.2.1.prime.not_dvd_mul
    · apply hp.2.1.prime.not_dvd_mul
      · exact hp.2.1.prime.not_dvd_mul (hplus 6 (by omega) (by simp [topIndex]))
          (hminus 4 (by omega) (by simp [topIndex]))
      · exact hplus 3 (by omega) (by simp [topIndex])
    · simpa only [fieldSize, pow_one] using hminus 1 (by omega) (by simp [topIndex])

/-- The same upper support bound holds after multiplying the characteristic
power and taking the exact central quotient. -/
theorem primitiveDivisor_not_dvd_order_of_large_index
    {x : RawEntry} {p f h l : ℕ} (hx : Admissible x) (hl : IsLie x)
    (hp : PrimitiveDivisor p h l) (hpbase : 2 ≤ p) (hf : 1 ≤ f)
    (hfield : fieldSize x = p ^ f) (hlarge : f * topIndex x < h) :
    ¬ l ∣ order x := by
  intro hd
  have hn : l ∣ numerator x := hd.trans (by
    rw [lie_order_eq hl]
    exact Nat.div_dvd_of_dvd (denominator_dvd_numerator hx))
  change l ∣ fieldSize x ^ characteristicExponent x * residual x at hn
  rcases hp.2.1.dvd_mul.mp hn with hchar | hres
  · rw [hfield, ← pow_mul] at hchar
    exact primitiveDivisor_not_dvd_power hp hpbase hchar
  · exact primitiveDivisor_not_dvd_residual_of_large_index hx hl hp hpbase hf hfield hlarge hres

end Atlas.OrderArithmetic
