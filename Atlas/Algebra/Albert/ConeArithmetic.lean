import Mathlib.Tactic

/-! Polynomial recombination of independently counted Albert coordinate strata. -/
namespace Atlas.Albert

theorem rankOne_count_polynomial (q : ℕ) (hq : 1≤q) :
    (q-1)*q^16 + (q-1)*((q^4+(q^4-1)*q^3)*q^8) +
      (q-1)*(q^4+(q^4-1)*q^3)^2 +
      (1+((q^4-1)*(q^3+1))*(2*q^4+1+(q^4-1)*q^3)) =
        1+(q^9-1)*(q^8+q^4+1) := by
  have h4 : 1≤q^4 := one_le_pow₀ hq
  have h9 : 1≤q^9 := one_le_pow₀ hq
  zify [hq,h4,h9]
  ring

theorem whiteZero_count_polynomial (q : ℕ) (hq : 1≤q) :
    (q-1)*((q^8-1)*q^7) +
      (q-1)*((q^4+(q^4-1)*q^3)*((q^4-1)*q^3)) +
      (1+((q^4-1)*(q^3+1))*(2*q^4+1+(q^4-1)*q^3)) =
        1+(q^12-1)*(q^4+1) := by
  have h4 : 1≤q^4 := one_le_pow₀ hq
  have h8 : 1≤q^8 := one_le_pow₀ hq
  have h12 : 1≤q^12 := one_le_pow₀ hq
  zify [hq,h4,h8,h12]
  ring

theorem traceOne_count_polynomial (q : ℕ) (hq : 1≤q) :
    (q^9-1)*(q^8+q^4+1) =
      (q^12-1)*(q^4+1) + (q-1)*(q^8*(q^8+q^4+1)) := by
  have h9 : 1≤q^9 := one_le_pow₀ hq
  have h12 : 1≤q^12 := one_le_pow₀ hq
  zify [hq,h9,h12]
  ring

end Atlas.Albert
