import Atlas.GroupTheory.IndexTwoNonsquareSimplicity
import Mathlib.Data.Nat.Prime.Basic

/-! Arithmetic for the prospective Tits order. These statements are numerical
only; they do not assert the cardinality or simplicity of any group. -/

namespace Atlas.Tits

/-- The candidate derived order is half the verified ambient stabilizer order. -/
theorem derived_order_arithmetic : 2 * 17971200 = (35942400 : ℕ) := by decide

/-- The candidate derived order has a prime factor 13 to odd valuation. -/
theorem derived_order_not_square (n : ℕ) : (17971200 : ℕ) ≠ n ^ 2 := by
  intro he
  have hp : Nat.Prime 13 := by decide
  have hd : 13 ∣ n ^ 2 := he ▸ (by decide : 13 ∣ (17971200 : ℕ))
  have hn : 13 ∣ n := hp.dvd_of_dvd_pow hd
  have hsq : 13 ^ 2 ∣ n ^ 2 := pow_dvd_pow_of_dvd hn 2
  rw [← he] at hsq
  exact (by decide : ¬(13 ^ 2 ∣ (17971200 : ℕ))) hsq

end Atlas.Tits
