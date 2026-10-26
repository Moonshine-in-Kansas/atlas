import Atlas.OrderArithmetic.Orders
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Parity

namespace Atlas.OrderArithmetic

/-- Syntactic normalization only; it never tests equality of orders. -/
def normalize : RawEntry → RawEntry
  | .linear d q =>
      if d = 2 ∧ (q = 4 ∨ q = 5) then .alternating 5
      else if d = 2 ∧ q = 9 then .alternating 6
      else if d = 3 ∧ q = 2 then .linear 2 7
      else if d = 4 ∧ q = 2 then .alternating 8
      else .linear d q
  | .unitary d q => if d = 4 ∧ q = 2 then .C 2 3 else .unitary d q
  | .B r q => if r = 2 ∨ (3 ≤ r ∧ Even q) then .C r q else .B r q
  | x => x

/-- The two stated unordered exceptions, independent of the order function. -/
def Exceptional (x y : RawEntry) : Prop :=
  (x = .alternating 8 ∧ y = .linear 3 4) ∨
  (y = .alternating 8 ∧ x = .linear 3 4) ∨
  ∃ r q : ℕ, 3 ≤ r ∧ PrimePower q ∧ Odd q ∧
    ((x = .B r q ∧ y = .C r q) ∨ (y = .B r q ∧ x = .C r q))

def Collision (x y : RawEntry) : Prop :=
  normalize x = normalize y ∨ Exceptional (normalize x) (normalize y)

theorem normalize_idempotent (x : RawEntry) : normalize (normalize x) = normalize x := by
  cases x <;> simp only [normalize]
  all_goals split_ifs <;> simp_all [normalize]
  all_goals split_ifs <;> simp_all

theorem normalize_admissible {x : RawEntry} (hx : Admissible x) :
    Admissible (normalize x) := by
  cases x <;> simp only [normalize]
  all_goals first | exact hx | skip
  all_goals split_ifs <;> simp_all [Admissible]
  · exact ⟨7, 1, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩

theorem order_linear_2_4 : order (.linear 2 4) = 60 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem order_linear_2_5 : order (.linear 2 5) = 60 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem order_linear_2_7 : order (.linear 2 7) = 168 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem order_linear_3_2 : order (.linear 3 2) = 168 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem order_linear_2_9 : order (.linear 2 9) = 360 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem order_linear_4_2 : order (.linear 4 2) = 20160 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem order_linear_3_4 : order (.linear 3 4) = 20160 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem order_unitary_4_2 : order (.unitary 4 2) = 25920 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    unitaryFactor, Finset.prod_Icc_succ_top]

theorem order_C_2_3 : order (.C 2 3) = 25920 := by
  norm_num [order, numerator, fieldSize, characteristicExponent, residual, denominator,
    Finset.prod_Icc_succ_top]

theorem normalize_order (x : RawEntry) : order (normalize x) = order x := by
  cases x with
  | linear d q =>
    simp only [normalize]
    split_ifs with h h h h
    · rcases h with ⟨rfl, rfl | rfl⟩
      · rw [order_linear_2_4]; norm_num [order, Nat.factorial]
      · rw [order_linear_2_5]; norm_num [order, Nat.factorial]
    · rcases h with ⟨rfl, rfl⟩
      rw [order_linear_2_9]; norm_num [order, Nat.factorial]
    · rcases h with ⟨rfl, rfl⟩
      rw [order_linear_3_2, order_linear_2_7]
    · rcases h with ⟨rfl, rfl⟩
      rw [order_linear_4_2]; norm_num [order, Nat.factorial]
    · rfl
  | unitary d q =>
    simp only [normalize]
    split_ifs with h
    · rcases h with ⟨rfl, rfl⟩
      rw [order_unitary_4_2, order_C_2_3]
    · rfl
  | B r q => simp only [normalize]; split_ifs <;> rfl
  | _ => rfl

theorem exceptional_order {x y : RawEntry} (h : Exceptional x y) : order x = order y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨r, q, _, _, _, h⟩
  · rw [order_linear_3_4]
    norm_num [order, Nat.factorial]
  · rw [order_linear_3_4]
    norm_num [order, Nat.factorial]
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The easy direction of the final classification, valid even without admissibility. -/
theorem collision_order {x y : RawEntry} (h : Collision x y) : order x = order y := by
  rw [← normalize_order x, ← normalize_order y]
  rcases h with h | h
  · rw [h]
  · exact exceptional_order h

end Atlas.OrderArithmetic
