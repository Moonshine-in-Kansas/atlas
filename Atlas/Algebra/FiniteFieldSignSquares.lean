import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Squares of powers of minus one over finite odd fields -/
noncomputable section
namespace Atlas
variable {F : Type*} [Field F] [Finite F]

theorem units_square_iff_field_square (a : Fˣ) :
    (∃ b : Fˣ, b^2 = a) ↔ IsSquare a.val := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.val, ?_⟩
    have h := congrArg Units.val hb
    simpa only [Units.val_pow_eq_pow_val, pow_two, Units.val_mul] using h.symm
  · rintro ⟨b, hb⟩
    have hbn : b ≠ 0 := by
      intro h
      apply a.ne_zero
      rw [hb, h, zero_mul]
    refine ⟨Units.mk0 b hbn, ?_⟩
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, Units.val_mul] using hb.symm

theorem odd_power_mod_four (q n : ℕ) (hq : q % 2 = 1) :
    q^n % 4 = if Even n then 1 else q % 4 := by
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases Nat.even_or_odd n with hn | hn
  · rw [if_pos hn]
    obtain ⟨k, hk⟩ := hn
    have he : n = 2*k := by omega
    rw [he, pow_mul]
    rcases hq4 with h | h <;> simp [Nat.pow_mod, h]
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn)]
    obtain ⟨k, hk⟩ := hn
    have he : n = 2*k+1 := by omega
    rw [he, pow_add, pow_mul]
    rcases hq4 with h | h <;> simp [Nat.mul_mod, Nat.pow_mod, h]

/-- The intrinsic square condition is exactly the advertised congruence. -/
theorem sign_power_square_iff_card_pow_mod_four (h2 : (2 : F) ≠ 0) (n : ℕ) :
    (∃ b : Fˣ, b^2 = (-1 : Fˣ)^n) ↔ Nat.card F ^ n % 4 = 1 := by
  classical
  letI := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have hz := CharP.cast_eq_zero F (ringChar F)
    rw [h] at hz
    exact hz
  have hodd : Nat.card F % 2 = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.odd_card_of_char_ne_two hchar
  rw [units_square_iff_field_square, Units.val_pow_eq_pow_val]
  change IsSquare ((-1 : F)^n) ↔ _
  rw [odd_power_mod_four _ _ hodd]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, if_pos hn]
    exact iff_of_true (IsSquare.one) rfl
  · rw [hn.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr hn), FiniteField.isSquare_neg_one_iff,
      ← Nat.card_eq_fintype_card]
    have hmod : Nat.card F % 4 < 4 := Nat.mod_lt _ (by decide)
    omega
theorem odd_card_mod_two (h2 : (2 : F) ≠ 0) : Nat.card F % 2 = 1 := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  apply FiniteField.odd_card_of_char_ne_two
  intro h
  apply h2
  have hz := CharP.cast_eq_zero F (ringChar F)
  rw [h] at hz
  exact hz

theorem twice_sign_center_factor (q n : ℕ) (hq : q % 2 = 1) :
    2 * (if q^n % 4 = 1 then 2 else 1) = Nat.gcd 4 (q^n-1) := by
  have hp : q^n % 2 = 1 := by simp [Nat.pow_mod, hq]
  have hmod := Nat.mod_lt (q^n) (by decide : 0 < 4)
  by_cases h : q^n % 4 = 1
  · have hx : (q^n-1) % 4 = 0 := by omega
    rw [if_pos h, Nat.gcd_rec, hx]
    norm_num
  · have hx : (q^n-1) % 4 = 2 := by omega
    rw [if_neg h, Nat.gcd_rec, hx]
    norm_num
end Atlas

