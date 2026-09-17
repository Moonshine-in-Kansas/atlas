import Mathlib.Data.Nat.ModEq

namespace Atlas.Algebra

/-- Five binary exponents with prescribed binary parity have precisely the
nonnegative even excess needed in the quintic contraction. -/
theorem binary_contraction_exponent (e d₀ d₁ d₂ d₃ d₄ : ℕ)
    (he : e ≤ 1) (h₀ : d₀ ≤ 1) (h₁ : d₁ ≤ 1) (h₂ : d₂ ≤ 1)
    (h₃ : d₃ ≤ 1) (h₄ : d₄ ≤ 1)
    (hp : (d₀ + d₁ + d₂ + d₃ + d₄) % 2 = e) :
    e ≤ d₀ + d₁ + d₂ + d₃ + d₄ ∧
      d₀ + d₁ + d₂ + d₃ + d₄ - e =
        2 * ((d₀ + d₁ + d₂ + d₃ + d₄ - e) / 2) ∧
      (d₀ + d₁ + d₂ + d₃ + d₄ - e) / 2 ≤ 2 := by
  omega

end Atlas.Algebra
