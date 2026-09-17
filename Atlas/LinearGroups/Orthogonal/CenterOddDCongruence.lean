import Atlas.LinearGroups.Orthogonal.CenterOddD
import Atlas.Algebra.FiniteFieldSignSquares

/-! # The odd split-D center in the q^n modulo four convention -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem negativeScalarD_mem_elementary_iff_mod_four (n : ℕ) (h2 : (2 : F) ≠ 0) :
    negativeScalarD (n+2) F ∈ elementarySubgroup (formD (n+2) F) ↔
      Nat.card F ^ (n+2) % 4 = 1 := by
  rw [negativeScalarD_mem_elementary_iff n h2, Atlas.sign_power_square_iff_card_pow_mod_four h2]

theorem card_elementaryD_center_mod_four (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.center (elementarySubgroup (formD (n+2) F))) =
      if Nat.card F ^ (n+2) % 4 = 1 then 2 else 1 := by
  rw [card_elementaryD_center n h2, Atlas.sign_power_square_iff_card_pow_mod_four h2]
  by_cases h : Nat.card F ^ (n+2) % 4 = 1 <;> simp [h]
theorem card_elementaryD_center_mul_two (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.center (elementarySubgroup (formD (n+2) F))) * 2 =
      Nat.gcd 4 (Nat.card F ^ (n+2)-1) := by
  rw [card_elementaryD_center_mod_four n h2, mul_comm]
  exact Atlas.twice_sign_center_factor _ _ (Atlas.odd_card_mod_two h2)
end Atlas.Orthogonal

