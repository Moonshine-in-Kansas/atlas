import Atlas.LinearGroups.Orthogonal.SpecialStandard
import Atlas.LinearGroups.Orthogonal.FullOrder

/-! # Uniform orders of the actual determinant-one groups -/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem card_specialB (n : ℕ) : Nat.card (SO_B n F) =
    Nat.card F ^ (n*n) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2*(i+1))-1) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have h := even_specialB_eq_top (n := n) (F := F)
    change Nat.card (specialSubgroup (formB n F)) = _
    rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv, card_fullB]
    simp only [if_pos h2, one_mul]
  · have h := card_specialB_mul_two (n := n) h2
    rw [card_fullB] at h
    simp only [if_neg h2] at h
    nlinarith

theorem card_specialD (n : ℕ) : Nat.card (SO_DPlus (n+1) F) =
    (if (2 : F) = 0 then 2 else 1) * Nat.card F ^ ((n+1)*n) *
      (Nat.card F ^ (n+1)-1) * ∏ i ∈ Finset.range n, (Nat.card F ^ (2*(i+1))-1) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    change Nat.card (specialSubgroup (formD (n+1) F)) = _
    rw [even_specialD_eq_top, Nat.card_congr Subgroup.topEquiv.toEquiv, card_fullD, if_pos h2]
  · have h := card_specialD_mul_sign (n := n+1) (F := F) (by omega)
    rw [card_fullD] at h
    simp only [if_neg h2] at h ⊢
    nlinarith

end Atlas.Orthogonal
