import Atlas.LinearGroups.Orthogonal.BAllRanksConstruction

/-! # Kernel-checked low-rank exception regressions on the actual B model -/
namespace Atlas.Orthogonal

theorem B1_two_order : Nat.card (B 1 (ZMod 2)) = 6 := by
  rw [B_card_all_rank 1 (by decide)]
  norm_num [B_order,B_order_numerator,B_order_denominator,Nat.card_zmod]

theorem B1_three_order : Nat.card (B 1 (ZMod 3)) = 12 := by
  rw [B_card_all_rank 1 (by decide)]
  norm_num [B_order,B_order_numerator,B_order_denominator,Nat.card_zmod]

theorem B1_two_not_simple : ¬ IsSimpleGroup (B 1 (ZMod 2)) := by
  rw [B_simple_iff_all_rank 1 (by decide)]
  simp [Nat.card_zmod]

theorem B1_three_not_simple : ¬ IsSimpleGroup (B 1 (ZMod 3)) := by
  rw [B_simple_iff_all_rank 1 (by decide)]
  simp [Nat.card_zmod]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem B1_five_simple : IsSimpleGroup (B 1 (ZMod 5)) := by
  apply B_simple_all_rank
  norm_num [B_good,Nat.card_zmod]
end Atlas.Orthogonal
