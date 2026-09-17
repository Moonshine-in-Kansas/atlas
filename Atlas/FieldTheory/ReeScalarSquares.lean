import Atlas.FieldTheory.ReeTitsAutomorphism
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem scalar_square_or_negative_square (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (a : F) :
    IsSquare a ∨ IsSquare (-a) := by
  classical
  letI := Fintype.ofFinite F
  have hn : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hcard]
    norm_num [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
  by_cases ha : IsSquare a
  · exact Or.inl ha
  right
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0,by simp⟩
  apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr ha0)).mp
  rw [show -a = (-1)*a by ring,map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr hn,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha]
  norm_num

theorem unit_eq_square_or_negative_square (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (l : Fˣ) :
    (∃ k : Fˣ, l = k^2) ∨ (∃ k : Fˣ, l = -(k^2)) := by
  rcases scalar_square_or_negative_square m hcard (l : F) with ⟨x,hx⟩ | ⟨x,hx⟩
  · left
    have hn : x ≠ 0 := by intro h; apply Units.ne_zero l; simpa [h] using hx
    refine ⟨Units.mk0 x hn, Units.ext ?_⟩
    simpa [pow_two] using hx
  · right
    have hn : x ≠ 0 := by
      intro h
      have hz : -(l : F) = 0 := by simpa [h] using hx
      exact Units.ne_zero l (neg_eq_zero.mp hz)
    refine ⟨Units.mk0 x hn, Units.ext ?_⟩
    simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, Units.val_mul]
    linear_combination -hx

end Atlas.ReeG2
