import Atlas.OrderArithmetic.Positivity
import Atlas.OrderArithmetic.ResidualInequalities
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Parity

namespace Atlas.OrderArithmetic
open scoped BigOperators

private theorem difference_of_squares {u : ℕ} (hu : 1 ≤ u) :
    u ^ 2 - 1 = (u - 1) * (u + 1) := by
  have h1 := Nat.sub_add_cancel hu
  have h2 := Nat.sub_add_cancel (Nat.one_le_pow 2 u hu)
  nlinarith

private theorem primePower_square {Q : ℕ} (hQ : PrimePower Q) : PrimePower (Q ^ 2) := by
  obtain ⟨p, f, hp, hf, rfl⟩ := hQ
  exact ⟨p, f * 2, hp, by omega, (pow_mul p f 2).symm⟩

/-- Exact cancellation before dividing by the two central denominators. -/
theorem linear_minus_numerator_ratio {Q r : ℕ} (hQ : 2 ≤ Q) (hr : 4 ≤ r) :
    numerator (.linear r (Q ^ 2)) * (Q ^ 2 - 1) =
      numerator (.Dminus r Q) * (Q ^ r - 1) := by
  let F : ℕ → ℕ := fun i => Q ^ (2 * i) - 1
  let P := ∏ i ∈ Finset.Icc 2 (r - 1), F i
  have hleftset : Finset.Icc 2 r = insert r (Finset.Icc 2 (r - 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hrightset : Finset.Icc 1 (r - 1) = insert 1 (Finset.Icc 2 (r - 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hleft : residual (.linear r (Q ^ 2)) = F r * P := by
    simp only [residual, ← pow_mul]
    rw [hleftset, Finset.prod_insert (by simp; omega)]
  have hright : residual (.Dminus r Q) = (Q ^ r + 1) * (F 1 * P) := by
    simp only [residual]
    rw [hrightset, Finset.prod_insert (by simp)]
  have hchar : (Q ^ 2) ^ (r * (r - 1) / 2) = Q ^ (r * (r - 1)) := by
    rw [← pow_mul, Nat.mul_comm 2, Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one r)]
  have htop : F r = (Q ^ r - 1) * (Q ^ r + 1) := by
    dsimp [F]
    rw [Nat.mul_comm 2 r, pow_mul]
    exact difference_of_squares (Nat.one_le_pow _ _ (by omega))
  have hbottom : F 1 = Q ^ 2 - 1 := by simp [F]
  simp only [numerator, fieldSize, characteristicExponent]
  rw [hchar, hleft, hright, htop, hbottom]
  ring

/-- Corresponding cancellation for the dimension-three/unitary-four residual pair. -/
theorem linear_unitary_numerator_ratio {Q : ℕ} (hQ : 2 ≤ Q) :
    numerator (.linear 3 (Q ^ 2)) * (Q ^ 2 - 1) =
      numerator (.unitary 4 Q) * (Q ^ 3 - 1) := by
  have h6 : Q ^ 6 - 1 = (Q ^ 3 - 1) * (Q ^ 3 + 1) := by
    rw [show Q ^ 6 = (Q ^ 3) ^ 2 by ring]
    exact difference_of_squares (Nat.one_le_pow _ _ (by omega))
  norm_num [numerator, fieldSize, characteristicExponent, residual, unitaryFactor,
    Finset.prod_Icc_succ_top, ← pow_mul]
  rw [h6]
  ring

private theorem central_ratio_of_order_eq {x y : RawEntry} {A B : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hratio : numerator x * A = numerator y * B) (he : order x = order y) :
    denominator x * A = denominator y * B := by
  have hnx : order x * denominator x = numerator x := by
    rw [lie_order_eq hlx]
    exact Nat.div_mul_cancel (denominator_dvd_numerator hx)
  have hny : order y * denominator y = numerator y := by
    rw [lie_order_eq hly]
    exact Nat.div_mul_cancel (denominator_dvd_numerator hy)
  rw [← hnx, ← hny, ← he, mul_assoc, mul_assoc] at hratio
  exact Nat.eq_of_mul_eq_mul_left (lie_order_pos hx hlx) hratio

/-- The two remaining classical order formulas are never equal in this branch. -/
theorem linear_square_ne_minus {Q r : ℕ} (hQ : PrimePower Q) (hr : 4 ≤ r) :
    order (.linear r (Q ^ 2)) ≠ order (.Dminus r Q) := by
  have hQ2 := primePower_two_le hQ
  have hx : Admissible (.linear r (Q ^ 2)) :=
    ⟨by omega, primePower_square hQ, by omega⟩
  have hy : Admissible (.Dminus r Q) := ⟨hr, hQ⟩
  intro he
  have h := central_ratio_of_order_eq hx hy (by trivial) (by trivial)
    (linear_minus_numerator_ratio hQ2 hr) he
  have hdL : denominator (.linear r (Q ^ 2)) ≤ r := Nat.gcd_le_left _ (by omega)
  have hdD : 1 ≤ denominator (.Dminus r Q) := denominator_pos hy
  have hupper := Nat.mul_le_mul_right (Q ^ 2 - 1) hdL
  have hlower := Nat.mul_le_mul_right (Q ^ r - 1) hdD
  have hgap := classical_residual_gap hQ2 hr
  nlinarith

/-- The other remaining classical order formulas are likewise distinct; Q=2
is settled by its literal numerical formulas. -/
theorem linear_three_square_ne_unitary_four {Q : ℕ} (hQ : PrimePower Q) :
    order (.linear 3 (Q ^ 2)) ≠ order (.unitary 4 Q) := by
  have hQ2 := primePower_two_le hQ
  by_cases htwo : Q = 2
  · subst Q
    norm_num [order, numerator, fieldSize, characteristicExponent, residual,
      denominator, unitaryFactor, Finset.prod_Icc_succ_top]
  have hx : Admissible (.linear 3 (Q ^ 2)) :=
    ⟨by omega, primePower_square hQ, by omega⟩
  have hy : Admissible (.unitary 4 Q) := ⟨by omega, hQ, by omega⟩
  intro he
  have h := central_ratio_of_order_eq hx hy (by trivial) (by trivial)
    (linear_unitary_numerator_ratio hQ2) he
  have hdL : denominator (.linear 3 (Q ^ 2)) ≤ 3 := Nat.gcd_le_left _ (by omega)
  have hdU : 1 ≤ denominator (.unitary 4 Q) := denominator_pos hy
  have hupper := Nat.mul_le_mul_right (Q ^ 2 - 1) hdL
  have hlower := Nat.mul_le_mul_right (Q ^ 3 - 1) hdU
  have hgap := unitary_linear_residual_gap (by omega : 3 ≤ Q)
  nlinarith

end Atlas.OrderArithmetic
