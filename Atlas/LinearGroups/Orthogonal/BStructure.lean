import Atlas.LinearGroups.Orthogonal.BConstruction
import Mathlib.GroupTheory.Index

/-! # Intrinsic index, center, and derived-subgroup interfaces for B -/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem B_elementary_card_mul_denominator (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (elementarySubgroup (formB n F)) * B_order_denominator (Nat.card F) =
      B_order_numerator n (Nat.card F) := by
  rw [← Nat.card_congr (B_elementaryEquiv (F := F) n hn).toEquiv]
  exact B_card_mul_denominator n hn

theorem B_elementary_index (n : ℕ) (hn : 2 ≤ n) :
    (elementarySubgroup (formB n F)).index =
      (if (2 : F) = 0 then 1 else 2) * B_order_denominator (Nat.card F) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := elementarySubgroup (formB n F)))
  rw [Subgroup.card_mul_index, card_fullB]
  have h := B_elementary_card_mul_denominator (F := F) n hn
  calc
    _ = (if (2 : F) = 0 then 1 else 2) * B_order_numerator n (Nat.card F) := by
      simp only [B_order_numerator,mul_assoc]
    _ = _ := by rw [← h]; ring

theorem B_center_order (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Subgroup.center (elementarySubgroup (formB n F))) = 1 := by
  rw [B_center_eq_bot n hn]
  exact Nat.card_unique

theorem B_scalar_order (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (elementaryScalarSubgroup (formB n F)) = 1 := by
  rw [B_scalar_eq_bot n hn]
  exact Nat.card_unique

/-- The intrinsic Omega convention agrees with the derived subgroup in the
advertised simple range. The exceptional B2(2) convention is not altered. -/
theorem B_elementary_eq_derived (n : ℕ) (hn : 2 ≤ n)
    (h : (n, Nat.card F) ≠ (2, 2)) :
    elementarySubgroup (formB n F) = commutator (O_B n F) := by
  by_cases h2 : (2 : F) = 0
  · apply le_antisymm
    · letI := B_elementary_perfect n hn h
      rw [← Subgroup.commutator_eq_self (H := elementarySubgroup (formB n F))]
      exact Subgroup.commutator_mono le_top le_top
    · rw [B_even_intrinsic n h2]
      exact le_top
  · obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
    exact elementaryB_eq_commutator k h2
end Atlas.Orthogonal
