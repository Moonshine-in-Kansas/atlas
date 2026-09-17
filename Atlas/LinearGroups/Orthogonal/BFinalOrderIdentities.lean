import Atlas.LinearGroups.Orthogonal.BAllRanksStructure
import Atlas.LinearGroups.Orthogonal.DStructureAllChar

/-! # Exact gcd-form full-order and index identities for the B family -/
open scoped Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

/-- The full orthogonal sign factor is precisely gcd(2,q-1). -/
theorem B_sign_factor_eq_gcd :
    (if (2 : F) = 0 then 1 else 2) = Nat.gcd 2 (Nat.card F - 1) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [if_pos h2,orthogonal_gcd_two_even]
  · rw [if_neg h2,orthogonal_gcd_two_odd h2]

/-- The actual full quadratic group has order d(q) S(n,q). -/
theorem B_full_order_gcd (n : ℕ) (_hn : 1 ≤ n) :
    Nat.card (O_B n F) =
      Nat.gcd 2 (Nat.card F - 1) * B_order_numerator n (Nat.card F) := by
  have h := card_fullB (F := F) n
  rw [← B_sign_factor_eq_gcd (F := F)]
  simpa only [B_order_numerator,mul_assoc] using h

/-- The actual elementary/intrinsic subgroup has full-group index d(q)^2. -/
theorem B_elementary_index_gcd_square (n : ℕ) (hn : 1 ≤ n) :
    (elementarySubgroup (formB n F)).index = Nat.gcd 2 (Nat.card F - 1)^2 := by
  rw [B_elementary_index_all_rank n hn,B_sign_factor_eq_gcd]
  simp only [B_order_denominator,pow_two]
end Atlas.Orthogonal
