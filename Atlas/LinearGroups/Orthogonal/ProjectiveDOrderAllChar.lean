import Atlas.LinearGroups.Orthogonal.ProjectiveOddD
import Atlas.LinearGroups.Orthogonal.EvenDOrder

/-! # Uniform exact projective split-D order in every finite characteristic -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

/-- In characteristic two the usual split-D denominator is one. -/
theorem evenD_order_denominator [CharP F 2] (r : ℕ) (hr : 0 < r) :
    Nat.gcd 4 (Nat.card F ^ r - 1) = 1 := by
  letI := Fintype.ofFinite F
  have hq : Nat.card F % 2 = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.even_card_of_char_two (ringChar.eq F 2)
  have hp : Nat.card F ^ r % 2 = 0 := by
    rw [Nat.pow_mod, hq, zero_pow (by omega : r ≠ 0)]
    rfl
  have hpos : 0 < Nat.card F ^ r := pow_pos Nat.card_pos _
  have ho : Odd (Nat.card F ^ r - 1) := by
    rw [Nat.odd_iff]
    omega
  have hc := ho.coprime_two_left.pow_left 2
  exact hc

/-- Multiplicative order identity, with the exact scalar denominator in every characteristic. -/
theorem card_projectiveD_all_char_mul_gcd (n : ℕ) :
    Nat.card (ProjectiveElementary (formD (n + 3) F)) * Nat.gcd 4 (Nat.card F ^ (n + 3) - 1) =
      Nat.card F ^ ((n + 3) * (n + 2)) * (Nat.card F ^ (n + 3) - 1) *
        ∏ i ∈ Finset.range (n + 2), (Nat.card F ^ (2 * (i + 1)) - 1) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [evenD_order_denominator _ (by omega), mul_one, card_evenProjectiveD]
  · exact card_projectiveElementaryD_mul_gcd (n + 1) h2

/-- Uniform order of the actual projective elementary split-D group in rank at least three. -/
theorem card_projectiveD_all_char (n : ℕ) :
    Nat.card (ProjectiveElementary (formD (n + 3) F)) =
      (Nat.card F ^ ((n + 3) * (n + 2)) * (Nat.card F ^ (n + 3) - 1) *
        ∏ i ∈ Finset.range (n + 2), (Nat.card F ^ (2 * (i + 1)) - 1)) /
      Nat.gcd 4 (Nat.card F ^ (n + 3) - 1) := by
  rw [← card_projectiveD_all_char_mul_gcd n,
    Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 4))]

end Atlas.Orthogonal
