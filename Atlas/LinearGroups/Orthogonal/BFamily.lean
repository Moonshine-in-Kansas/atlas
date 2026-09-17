import Atlas.Algebra.FiniteFieldSignSquares
import Atlas.LinearGroups.Orthogonal.ProjectiveOddB
import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB

/-! # Actual projective B model and independent finite order, rank at least two -/
noncomputable section
namespace Atlas.Orthogonal

abbrev B (n : ℕ) (F : Type*) [Field F] := ProjectiveElementary (formB n F)
def B_order_numerator (n q : ℕ) : ℕ :=
  q ^ (n * n) * ∏ i ∈ Finset.range n, (q ^ (2 * (i + 1)) - 1)
def B_order_denominator (q : ℕ) : ℕ := Nat.gcd 2 (q - 1)
def B_order (n q : ℕ) : ℕ := B_order_numerator n q / B_order_denominator q
/-- The rank-at-least-two simple range. Rank one is handled separately. -/
def B_admissible (n q : ℕ) : Prop := 2 ≤ n ∧ 2 ≤ q ∧ (n, q) ≠ (2, 2)
theorem B_order_denominator_positive (q : ℕ) : 0 < B_order_denominator q :=
  Nat.gcd_pos_of_pos_left _ (by decide : 0 < 2)
theorem B_order_numerator_positive (n q : ℕ) (hq : 2 ≤ q) :
    0 < B_order_numerator n q := by
  apply Nat.mul_pos (pow_pos (by omega) _)
  apply Finset.prod_pos
  intro i hi
  exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega : 1 < q) (by omega : 2 * (i + 1) ≠ 0))

variable {F : Type*} [Field F] [Finite F]

theorem B_finite (n : ℕ) : Finite (B n F) := inferInstance

theorem B_card_mul_denominator (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (B n F) * B_order_denominator (Nat.card F) = B_order_numerator n (Nat.card F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have he : B_order_denominator (Nat.card F) = 1 := by
      letI := Fintype.ofFinite F
      have hq : Nat.card F % 2 = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.even_card_of_char_two (ringChar.eq F 2)
      have ho : Odd (Nat.card F - 1) := by
        rw [Nat.odd_iff]
        have hp : 0 < Nat.card F := Nat.card_pos
        omega
      exact ho.coprime_two_left
    rw [he,mul_one]
    exact card_evenProjectiveB (k + 2)
  · have he : B_order_denominator (Nat.card F) = 2 := by
      have h := Atlas.odd_card_mod_two h2
      exact Nat.gcd_eq_left (by omega)
    rw [he]
    exact card_projectiveElementaryB_mul_two k h2

theorem B_order_divisibility (n : ℕ) (hn : 2 ≤ n) :
    B_order_denominator (Nat.card F) ∣ B_order_numerator n (Nat.card F) :=
  ⟨Nat.card (B n F),(B_card_mul_denominator n hn).symm.trans (Nat.mul_comm _ _)⟩

theorem B_card (n : ℕ) (hn : 2 ≤ n) : Nat.card (B n F) = B_order n (Nat.card F) := by
  unfold B_order
  rw [← B_card_mul_denominator n hn,
    Nat.mul_div_cancel _ (B_order_denominator_positive (Nat.card F))]

end Atlas.Orthogonal
