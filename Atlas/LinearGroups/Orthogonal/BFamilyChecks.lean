import Atlas.LinearGroups.Orthogonal.SimplicityCompleteB
import Atlas.LinearGroups.Orthogonal.OrderAllCharB

/-! # Small-field checks of the actual B carrier and the exact exceptional model -/
noncomputable section
namespace Atlas.Orthogonal

theorem B2_three_simple : IsSimpleGroup (ProjectiveElementary (formB 2 (ZMod 3))) := by
  apply projectiveB_two_simple
  decide

theorem B2_two_not_simple : ¬ IsSimpleGroup (ProjectiveElementary (formB 2 (ZMod 2))) := by
  rw [projectiveB_simple_iff 0]
  simp [Nat.card_eq_fintype_card]

theorem B2_three_order : Nat.card (ProjectiveElementary (formB 2 (ZMod 3))) = 25920 := by
  rw [card_projectiveB_all_char 0]
  norm_num [Nat.card_eq_fintype_card, Finset.prod_range_succ,
    show (2 : ZMod 3) ≠ 0 by decide]

theorem B2_two_order : Nat.card (ProjectiveElementary (formB 2 (ZMod 2))) = 720 := by
  rw [card_projectiveB_all_char 0]
  rw [if_pos (show (2 : ZMod 2) = 0 by decide)]
  norm_num [Nat.card_eq_fintype_card, Finset.prod_range_succ]
end Atlas.Orthogonal
