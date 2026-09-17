import Atlas.LinearGroups.Orthogonal.OrderBase
import Atlas.LinearGroups.Orthogonal.OrderRecurrence

/-! # Uniform orders of the full B and split D quadratic isometry groups -/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem card_fullB (n : ℕ) : Nat.card (O_B n F) =
    (if (2 : F) = 0 then 1 else 2) * Nat.card F ^ (n*n) *
      ∏ i ∈ Finset.range n, (Nat.card F ^ (2*(i+1)) - 1) := by
  induction n with
  | zero => simp only [card_fullB_zero, Nat.mul_zero, pow_zero, mul_one, Finset.range_zero, Finset.prod_empty]
  | succ n ih =>
    rw [card_fullB_succ, ih, Finset.prod_range_succ]
    have he : 2*(n+1)-1 = 2*n+1 := by omega
    have hn : (n+1)*(n+1) = (2*n+1)+n*n := by ring
    rw [he, hn, pow_add]
    ring

/-- A natural-number factorization used in the split-D order recurrence. -/
theorem difference_square (a : ℕ) (ha : 1 ≤ a) : (a+1)*(a-1) = a^2-1 := by
  have h : a-1+1 = a := Nat.sub_add_cancel ha
  have he : a^2 = (a+1)*(a-1)+1 := by nlinarith
  omega

theorem card_fullD (n : ℕ) : Nat.card (O_DPlus (n+1) F) =
    2 * Nat.card F ^ ((n+1)*n) * (Nat.card F ^ (n+1)-1) *
      ∏ i ∈ Finset.range n, (Nat.card F ^ (2*(i+1))-1) := by
  induction n with
  | zero =>
    rw [card_fullD_succ, card_fullD_zero]
    simp only [Nat.mul_zero, pow_zero, pow_one, Finset.range_zero, Finset.prod_empty, mul_one]
    ring
  | succ n ih =>
    rw [card_fullD_succ, ih, Finset.prod_range_succ]
    have hq : 1 ≤ Nat.card F := Nat.card_pos
    have hp : 1 ≤ Nat.card F ^ (n+1) := one_le_pow₀ hq
    have hd : (Nat.card F ^ (n+1)+1)*(Nat.card F ^ (n+1)-1) =
        Nat.card F ^ (2*(n+1))-1 := by
      rw [difference_square _ hp, ← pow_mul]
      congr 2
      omega
    have hn : (n+1+1)*(n+1) = 2*(n+1)+(n+1)*n := by ring
    rw [hn, pow_add (Nat.card F) (2*(n+1)) ((n+1)*n)]
    calc
      _ = 2 * (Nat.card F ^ (2*(n+1)) * Nat.card F ^ ((n+1)*n)) *
          (Nat.card F ^ (n+1+1)-1) *
          ((∏ i ∈ Finset.range n, (Nat.card F ^ (2*(i+1))-1)) *
            ((Nat.card F ^ (n+1)+1)*(Nat.card F ^ (n+1)-1))) := by ring
      _ = _ := by rw [hd]

end Atlas.Orthogonal
