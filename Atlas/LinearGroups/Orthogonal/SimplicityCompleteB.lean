import Atlas.LinearGroups.Orthogonal.SimplicityRankTwoB
import Atlas.LinearGroups.Orthogonal.SimplicityAllCharB

/-! # Exact simplicity range of the actual projective B carrier, rank at least two -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem projectiveB_simple_iff (n : ℕ) :
    IsSimpleGroup (ProjectiveElementary (formB (n + 2) F)) ↔
      (n + 2, Nat.card F) ≠ (2, 2) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact even_projectiveB_simple_iff_rank_ge_two (by omega)
  · have hs : IsSimpleGroup (ProjectiveElementary (formB (n + 2) F)) := by
      cases n with
      | zero => exact projectiveB_two_simple h2
      | succ n => exact projectiveB_simple_all_char n
    have hn : (n + 2, Nat.card F) ≠ (2, 2) := by
      intro he
      have hq := congrArg Prod.snd he
      have ho := Atlas.odd_card_mod_two h2
      simp only [Prod.snd] at hq
      omega
    exact iff_of_true hs hn

theorem projectiveB_noncommutative (n : ℕ)
    (h : (n + 2, Nat.card F) ≠ (2, 2)) :
    ¬ IsMulCommutative (ProjectiveElementary (formB (n + 2) F)) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact even_projectiveB_noncommutative (Or.inr ⟨by omega, h⟩)
  · exact projectiveElementaryB_noncommutative n h2
end Atlas.Orthogonal
