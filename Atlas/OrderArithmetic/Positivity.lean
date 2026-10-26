import Atlas.OrderArithmetic.Valuations
import Mathlib.Tactic.Positivity

namespace Atlas.OrderArithmetic

theorem characteristicExponent_pos {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    1 ≤ characteristicExponent x := by
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear d q | unitary d q =>
    have hd : 2 ≤ d := by have := hx.1; omega
    have hsub : 1 ≤ d - 1 := by omega
    have hm : 2 ≤ d * (d - 1) := by
      simpa using Nat.mul_le_mul hd hsub
    change 1 ≤ d * (d - 1) / 2
    omega
  | B r q | C r q =>
    have hr : 2 ≤ r := hx.1
    change 1 ≤ r ^ 2
    exact Nat.one_le_pow _ _ (by omega)
  | Dplus r q | Dminus r q =>
    have hr : 4 ≤ r := hx.1
    change 1 ≤ r * (r - 1)
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  | _ => norm_num [characteristicExponent]

theorem residual_pos {x : RawEntry} (hx : Admissible x) (hl : IsLie x) : 0 < residual x := by
  obtain ⟨p, f, hp, hf, hq⟩ := lie_field_primePower hx hl
  have hn := characteristic_not_dvd_residual hx hl hp (hq ▸ dvd_pow_self _ (by omega))
  exact Nat.pos_of_ne_zero fun hz => hn (hz ▸ dvd_zero p)

theorem lie_order_pos {x : RawEntry} (hx : Admissible x) (hl : IsLie x) : 0 < order x := by
  have hq := primePower_two_le (lie_field_primePower hx hl)
  have hr := residual_pos hx hl
  have hn : 0 < numerator x := Nat.mul_pos (pow_pos (by omega) _) hr
  rw [lie_order_eq hl]
  exact Nat.div_pos (Nat.le_of_dvd hn (denominator_dvd_numerator hx)) (denominator_pos hx)

theorem characteristic_power_dvd_order {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    fieldSize x ^ characteristicExponent x ∣ order x := by
  rw [lie_order_eq hl, numerator, quotient_factorization (denominator_dvd_residual hx)]
  exact dvd_mul_right _ _

end Atlas.OrderArithmetic
