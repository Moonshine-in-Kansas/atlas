import Atlas.LinearGroups.Orthogonal.ProjectiveDOrderAllChar
import Mathlib.GroupTheory.Index

/-! # Uniform elementary orders, indices and actual scalar centers for split D -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem orthogonal_gcd_two_odd (h2 : (2 : F) ≠ 0) :
    Nat.gcd 2 (Nat.card F - 1) = 2 := by
  have h := Atlas.odd_card_mod_two h2
  exact Nat.gcd_eq_left (by omega)

theorem orthogonal_gcd_two_even [CharP F 2] : Nat.gcd 2 (Nat.card F - 1) = 1 := by
  have h := evenD_order_denominator (F := F) 1 (by decide)
  have hc : Nat.Coprime 4 (Nat.card F - 1) := by simpa only [pow_one] using h
  exact hc.of_dvd_left (by decide : 2 ∣ 4)

/-- Uniform elementary order, with its intrinsic index factor retained. -/
theorem card_elementaryD_all_char_mul_gcd_two (n : ℕ) :
    Nat.card (elementarySubgroup (formD (n + 3) F)) * Nat.gcd 2 (Nat.card F - 1) =
      Nat.card F ^ ((n + 3) * (n + 2)) * (Nat.card F ^ (n + 3) - 1) *
        ∏ i ∈ Finset.range (n + 2), (Nat.card F ^ (2 * (i + 1)) - 1) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [orthogonal_gcd_two_even, mul_one, card_evenElementaryD]
  · rw [orthogonal_gcd_two_odd h2]
    exact card_elementaryD_mul_two (n + 1) h2

/-- The full-group index of the actual elementary subgroup is twice gcd(2,q-1). -/
theorem elementaryD_index_all_char (n : ℕ) :
    (elementarySubgroup (formD (n + 3) F)).index = 2 * Nat.gcd 2 (Nat.card F - 1) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := elementarySubgroup (formD (n + 3) F)))
  rw [Subgroup.card_mul_index]
  have he := card_elementaryD_all_char_mul_gcd_two (F := F) n
  rw [card_fullD (n + 2)]
  calc
    _ = 2 * (Nat.card (elementarySubgroup (formD (n + 3) F)) *
        Nat.gcd 2 (Nat.card F - 1)) := by rw [he]; ring
    _ = _ := by ring

/-- The actual scalar center has the standard uniform cardinality factor. -/
theorem card_elementaryD_center_all_char_mul_gcd_two (n : ℕ) :
    Nat.card (Subgroup.center (elementarySubgroup (formD (n + 3) F))) *
      Nat.gcd 2 (Nat.card F - 1) = Nat.gcd 4 (Nat.card F ^ (n + 3) - 1) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [elementaryD_center_eq_bot_of_two_eq_zero (n + 1) h2,
      Nat.card_unique,
      orthogonal_gcd_two_even, one_mul, evenD_order_denominator _ (by omega)]
  · rw [orthogonal_gcd_two_odd h2]
    exact card_elementaryD_center_mul_two (n + 1) h2

omit [Finite F] in
/-- Equality of subgroups, not merely a cardinality calculation. -/
theorem elementaryD_scalar_eq_center (n : ℕ) :
    elementaryScalarSubgroup (formD (n + 3) F) =
      Subgroup.center (elementarySubgroup (formD (n + 3) F)) :=
  elementaryScalarSubgroup_eq_center _ (wittTwoFrameD (n + 1)) polarD_nondegenerate

/-- The public scalar quotient is actually isomorphic to quotienting by the full center. -/
def projectiveDQuotientCenterEquiv (n : ℕ) :
    ProjectiveElementary (formD (n + 3) F) ≃*
      (elementarySubgroup (formD (n + 3) F) ⧸
        Subgroup.center (elementarySubgroup (formD (n + 3) F))) :=
  projectiveElementaryCenterEquiv _ (wittTwoFrameD (n + 1)) polarD_nondegenerate

/-- Uniform exact order of the actual elementary carrier. -/
theorem card_elementaryD_all_char (n : ℕ) :
    Nat.card (elementarySubgroup (formD (n + 3) F)) =
      (Nat.card F ^ ((n + 3) * (n + 2)) * (Nat.card F ^ (n + 3) - 1) *
        ∏ i ∈ Finset.range (n + 2), (Nat.card F ^ (2 * (i + 1)) - 1)) /
      Nat.gcd 2 (Nat.card F - 1) := by
  rw [← card_elementaryD_all_char_mul_gcd_two n,
    Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 2))]

/-- The full scalar subgroup has the same exact center factor. -/
theorem card_elementaryD_scalar_all_char_mul_gcd_two (n : ℕ) :
    Nat.card (elementaryScalarSubgroup (formD (n + 3) F)) *
      Nat.gcd 2 (Nat.card F - 1) = Nat.gcd 4 (Nat.card F ^ (n + 3) - 1) := by
  rw [elementaryD_scalar_eq_center, card_elementaryD_center_all_char_mul_gcd_two]

/-- Exact cardinality of the actual center, with both gcd factors visible. -/
theorem card_elementaryD_center_all_char (n : ℕ) :
    Nat.card (Subgroup.center (elementarySubgroup (formD (n + 3) F))) =
      Nat.gcd 4 (Nat.card F ^ (n + 3) - 1) / Nat.gcd 2 (Nat.card F - 1) := by
  rw [← card_elementaryD_center_all_char_mul_gcd_two n,
    Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 2))]
end Atlas.Orthogonal
