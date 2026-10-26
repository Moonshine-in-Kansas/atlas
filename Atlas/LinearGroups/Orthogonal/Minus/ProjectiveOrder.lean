import Atlas.LinearGroups.Orthogonal.Minus.ElementaryOrder
import Atlas.LinearGroups.Orthogonal.Minus.CenterOdd

/-! Uniform projective order from actual kernel indices and the actual scalar center. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem card_elementary_odd_mul_two (hdeg : Module.finrank F K = 2) (n : ℕ)
    (h2 : (2 : F) ≠ 0) :
    Nat.card (E hdeg (n+2)) * 2 =
      Nat.card F ^ ((n+3)*(n+2)) * (Nat.card F ^ (n+3)+1) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1) := by
  have h := card_elementary_mul_four hdeg n h2
  rw [card_full] at h
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
  calc
    Nat.card (E hdeg (n+2)) * 2 * 2 = Nat.card (E hdeg (n+2)) * 4 := by ring
    _ = _ := h
    _ = _ := by ring

theorem card_projective_odd_mul_gcd (hdeg : Module.finrank F K = 2) (n : ℕ)
    (h2 : (2 : F) ≠ 0) :
    Nat.card (ProjectiveElementary (form hdeg (n+2))) * Nat.gcd 4 (Nat.card F^(n+3)+1) =
      Nat.card F ^ ((n+3)*(n+2)) * (Nat.card F ^ (n+3)+1) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1) := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (elementaryScalarSubgroup (form hdeg (n+2)))
  change Nat.card (E hdeg (n+2)) = Nat.card (ProjectiveElementary (form hdeg (n+2))) *
    Nat.card (elementaryScalarSubgroup (form hdeg (n+2))) at hc
  rw [elementaryScalarSubgroup_eq_center _ (wittTwoFrame hdeg n) (polar_nondegenerate hdeg _)] at hc
  rw [← card_elementary_center_mul_two hdeg n h2,← mul_assoc,← hc]
  exact card_elementary_odd_mul_two hdeg n h2

theorem even_order_denominator [CharP F 2] (r : ℕ) (hr : 0 < r) :
    Nat.gcd 4 (Nat.card F ^ r + 1) = 1 := by
  letI := Fintype.ofFinite F
  have hq : Nat.card F % 2 = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.even_card_of_char_two (ringChar.eq F 2)
  have hp : Nat.card F ^ r % 2 = 0 := by
    rw [Nat.pow_mod,hq,zero_pow (by omega : r ≠ 0)]
    rfl
  have ho : Odd (Nat.card F ^ r + 1) := by
    rw [Nat.odd_iff]
    omega
  exact ho.coprime_two_left.pow_left 2

theorem card_projective_mul_gcd (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (ProjectiveElementary (form hdeg (n+2))) * Nat.gcd 4 (Nat.card F^(n+3)+1) =
      Nat.card F ^ ((n+3)*(n+2)) * (Nat.card F ^ (n+3)+1) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [even_order_denominator _ (by omega),mul_one,card_projective_even]
  · exact card_projective_odd_mul_gcd hdeg n h2

theorem card_projective (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (ProjectiveElementary (form hdeg (n+2))) =
      (Nat.card F ^ ((n+3)*(n+2)) * (Nat.card F ^ (n+3)+1) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1)) /
          Nat.gcd 4 (Nat.card F^(n+3)+1) := by
  rw [← card_projective_mul_gcd hdeg n,
    Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 4))]
end Atlas.Orthogonal.Minus
