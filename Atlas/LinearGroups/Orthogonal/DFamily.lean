import Atlas.LinearGroups.Orthogonal.ProjectiveDOrderAllChar

/-! # The public split-D carrier and its independent order interface

The public rank range is n ≥ 4. The model is transparently the scalar quotient
of the elementary subgroup of the actual split quadratic form on 2n coordinates.
This module does not import simplicity results.
-/
noncomputable section
namespace Atlas.Orthogonal

/-- Actual projective elementary split orthogonal group on 2n coordinates. -/
abbrev DPlus (n : ℕ) (F : Type*) [Field F] := ProjectiveElementary (formD n F)

/-- Independent numerical numerator for the split-D order. -/
def DPlus_order_numerator (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n - 1) *
    ∏ i ∈ Finset.range (n - 1), (q ^ (2 * (i + 1)) - 1)

def DPlus_order_denominator (n q : ℕ) : ℕ := Nat.gcd 4 (q ^ n - 1)

def DPlus_order (n q : ℕ) : ℕ := DPlus_order_numerator n q / DPlus_order_denominator n q

/-- The advertised simple-family range has no exceptional finite field. -/
def DPlus_admissible (n q : ℕ) : Prop := 4 ≤ n ∧ 2 ≤ q

theorem DPlus_order_denominator_positive (n q : ℕ) : 0 < DPlus_order_denominator n q :=
  Nat.gcd_pos_of_pos_left _ (by decide : 0 < 4)

theorem DPlus_order_numerator_positive (n q : ℕ) (hn : 4 ≤ n) (hq : 2 ≤ q) :
    0 < DPlus_order_numerator n q := by
  unfold DPlus_order_numerator
  apply Nat.mul_pos
  · apply Nat.mul_pos (pow_pos (by omega) _)
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega : 1 < q) (by omega : n ≠ 0))
  · apply Finset.prod_pos
    intro i hi
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega : 1 < q) (by omega : 2 * (i + 1) ≠ 0))

variable {F : Type*} [Field F] [Finite F]

theorem DPlus_finite (n : ℕ) (_hn : 4 ≤ n) : Finite (DPlus n F) := inferInstance

theorem DPlus_card_mul_denominator (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (DPlus n F) * DPlus_order_denominator n (Nat.card F) =
      DPlus_order_numerator n (Nat.card F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  simpa only [DPlus_order_denominator,DPlus_order_numerator,show k + 3 - 1 = k + 2 by omega]
    using card_projectiveD_all_char_mul_gcd (F := F) k

theorem DPlus_order_divisibility (n : ℕ) (hn : 4 ≤ n) :
    DPlus_order_denominator n (Nat.card F) ∣ DPlus_order_numerator n (Nat.card F) := by
  refine ⟨Nat.card (DPlus n F), ?_⟩
  exact (DPlus_card_mul_denominator n hn).symm.trans (Nat.mul_comm _ _)

theorem DPlus_card (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (DPlus n F) = DPlus_order n (Nat.card F) := by
  unfold DPlus_order
  rw [← DPlus_card_mul_denominator n hn,
    Nat.mul_div_cancel _ (DPlus_order_denominator_positive n (Nat.card F))]

end Atlas.Orthogonal
