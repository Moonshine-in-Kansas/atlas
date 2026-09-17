import Atlas.Algebra.FiniteFieldSignSquares
import Atlas.LinearGroups.Orthogonal.ProjectiveOddB
import Atlas.LinearGroups.Symplectic.ProjectiveOrder

/-! # Equal orders do not identify the odd-characteristic B and C models -/
namespace Atlas.Comparisons.Classical
open Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem oddB_card_eq_C (n : ℕ) (hn : 2 ≤ n) (h2 : (2 : F) ≠ 0) :
    Nat.card (ProjectiveElementary (formB n F)) = Nat.card (Atlas.Symplectic.PSp n F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 k]
  have ho := Atlas.odd_card_mod_two h2
  letI := Fintype.ofFinite F
  have hq : 1 < Nat.card F := by simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
  have hd : Nat.gcd 2 (Nat.card F - 1) = 2 := by
    apply Nat.gcd_eq_left_iff_dvd.mpr
    omega
  rw [card_projectiveElementaryB k h2, Atlas.Symplectic.card_psp (by omega), hd]
  rfl
end Atlas.Comparisons.Classical
