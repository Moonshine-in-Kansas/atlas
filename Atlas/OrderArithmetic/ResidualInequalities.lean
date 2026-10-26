import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace Atlas.OrderArithmetic

/-- The residual L_r(Q²)/Dminus_r(Q) equality is impossible for r ≥ 4. -/
theorem classical_residual_gap {Q r : ℕ} (hQ : 2 ≤ Q) (hr : 4 ≤ r) :
    r * (Q ^ 2 - 1) < Q ^ r - 1 := by
  have hQ2 : 4 ≤ Q ^ 2 := by nlinarith
  have hs := Nat.sub_add_cancel (by omega : 1 ≤ Q ^ 2)
  induction r, hr using Nat.le_induction with
  | base =>
    have hpow : Q ^ 4 = (Q ^ 2) ^ 2 := by ring
    have hpos : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
    have := Nat.sub_add_cancel hpos
    nlinarith [sq_nonneg (Q ^ 2 - 4 : ℤ)]
  | succ r hr ih =>
    have hp : 1 ≤ Q ^ r := Nat.one_le_pow _ _ (by omega)
    have hnext : 1 ≤ Q ^ (r + 1) := Nat.one_le_pow _ _ (by omega)
    have hsub := Nat.sub_add_cancel hp
    have hsubnext := Nat.sub_add_cancel hnext
    rw [pow_succ] at hsubnext
    have hg : 2 * Q ^ r ≤ Q ^ r * Q := by nlinarith
    have hh : Q ^ 2 - 1 ≤ r * (Q ^ 2 - 1) := by
      exact Nat.le_mul_of_pos_left _ (by omega)
    rw [pow_succ Q r]
    nlinarith

/-- The other residual comparison is excluded for Q ≥ 3. -/
theorem unitary_linear_residual_gap {Q : ℕ} (hQ : 3 ≤ Q) :
    3 * (Q ^ 2 - 1) < Q ^ 3 - 1 := by
  have hsq : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcu : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hs := Nat.sub_add_cancel hsq
  have hc := Nat.sub_add_cancel hcu
  have hmul : 3 * Q ^ 2 ≤ Q ^ 3 := by
    rw [pow_succ]
    nlinarith
  omega

end Atlas.OrderArithmetic
