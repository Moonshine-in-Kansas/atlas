import Atlas.OrderArithmetic.HighRankUnitaryOrthogonal
import Mathlib.Tactic.Zify

namespace Atlas.OrderArithmetic

/-- The degree-four plus factor, written without a truncated subtraction. -/
def trialityPlusFactor (q : ℕ) : ℕ := q ^ 2 * (q ^ 2 - 1) + 1

theorem trialityPlusFactor_odd (q : ℕ) : Odd (trialityPlusFactor q) :=
  (Nat.even_mul_pred_self (q ^ 2)).add_odd (by decide : Odd (1 : ℕ))

theorem trialityPlusFactor_dvd_plus_six {q : ℕ} (hq : 2 ≤ q) :
    trialityPlusFactor q ∣ q ^ 6 + 1 := by
  have hs : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨q ^ 2 + 1, ?_⟩
  unfold trialityPlusFactor
  zify [hs]
  ring

/-- Exact refactorization into two pieces with disjoint prime supports. -/
theorem triality_residual_eq_proxy {q : ℕ} (hq : 2 ≤ q) :
    residual (.trialityD4 q) = (q ^ 6 - 1) ^ 2 * trialityPlusFactor q := by
  have hs2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hs6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold residual trialityPlusFactor
  zify [hs2, hs6]
  ring

theorem triality_residual_dvd_proxy {q : ℕ} (hq : 2 ≤ q) :
    residual (.trialityD4 q) ∣ (q ^ 6 - 1) ^ 2 * trialityPlusFactor q := by
  rw [triality_residual_eq_proxy hq]

theorem trialityPlusFactor_le_fourth {q : ℕ} (hq : 2 ≤ q) :
    trialityPlusFactor q ≤ q ^ 4 := by
  have hs : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold trialityPlusFactor
  have hh : q ^ 2 * (q ^ 2 - 1) + q ^ 2 = q ^ 4 := by
    calc
      _ = q ^ 2 * ((q ^ 2 - 1) + 1) := by ring
      _ = q ^ 4 := by rw [Nat.sub_add_cancel hs]; ring
  omega

theorem triality_prime_support_disjoint {q l : ℕ} (hq : 2 ≤ q) (hl : l.Prime)
    (hplus : l ∣ trialityPlusFactor q) : ¬ l ∣ q ^ 6 - 1 := by
  intro hminus
  have hh := hplus.trans (trialityPlusFactor_dvd_plus_six hq)
  have hd := Nat.dvd_sub hh hminus
  have hs : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have he : q ^ 6 + 1 - (q ^ 6 - 1) = 2 := by omega
  rw [he] at hd
  have hl2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd
  rw [hl2] at hplus
  have hz := Nat.mod_eq_zero_of_dvd hplus
  have ho := Nat.odd_iff.mp (trialityPlusFactor_odd q)
  omega

/-- Full cross-prime dominance for the triality order, from two coprime
residual pieces rather than an overestimate by the entire residual. -/
theorem trialityD4_cross_contribution_lt {q l : ℕ}
    (hx : Admissible (.trialityD4 q)) (hl : l.Prime) (hlq : ¬ l ∣ q) :
    l ^ (order (.trialityD4 q)).factorization l < q ^ 12 := by
  have hq : 2 ≤ q := primePower_two_le hx
  have hd := (cross_prime_order_contribution_dvd_residual hx (by trivial) hl hlq).trans
    (triality_residual_dvd_proxy hq)
  by_cases hb : l ∣ trialityPlusFactor q
  · have hn : ¬ l ∣ (q ^ 6 - 1) ^ 2 := fun hh =>
      triality_prime_support_disjoint hq hl hb (hl.dvd_of_dvd_pow hh)
    have hdB := hl.prime.pow_dvd_of_dvd_mul_left _ hn hd
    have hBpos : 0 < trialityPlusFactor q := by unfold trialityPlusFactor; omega
    have hle := (Nat.le_of_dvd hBpos hdB).trans (trialityPlusFactor_le_fourth hq)
    exact hle.trans_lt ((Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mpr (by decide : 4 < 12))
  · have hdA := hl.prime.pow_dvd_of_dvd_mul_right _ hb hd
    have hq6 : 1 < q ^ 6 := by
      have hh : q ≤ q ^ 6 := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 1 ≤ 6)
      omega
    have hle := Nat.le_of_dvd (pow_pos (by omega : 0 < q ^ 6 - 1) 2) hdA
    have hlt : (q ^ 6 - 1) ^ 2 < (q ^ 6) ^ 2 :=
      Nat.pow_lt_pow_left (by omega) (by decide)
    have hp : (q ^ 6) ^ 2 = q ^ 12 := by rw [← pow_mul]
    exact hle.trans_lt (hp ▸ hlt)

end Atlas.OrderArithmetic
