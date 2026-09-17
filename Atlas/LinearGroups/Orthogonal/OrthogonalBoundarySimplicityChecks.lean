import Atlas.LinearGroups.Orthogonal.BAllRanksConstruction
import Atlas.LinearGroups.Orthogonal.DConstruction

/-! # Required binary, ternary and genuine nonprime-field simplicity regressions -/
namespace Atlas.Orthogonal.Checks

theorem b3_two_simple : IsSimpleGroup (B 3 (ZMod 2)) := by
  apply B_simple_all_rank
  norm_num [B_good,Nat.card_zmod]

theorem b3_three_simple : IsSimpleGroup (B 3 (ZMod 3)) := by
  apply B_simple_all_rank
  norm_num [B_good,Nat.card_zmod]

theorem b3_four_simple : IsSimpleGroup (B 3 (GaloisField 2 2)) := by
  have hq : Nat.card (GaloisField 2 2) = 4 := by
    simpa using GaloisField.card 2 2 (by decide)
  apply B_simple_all_rank
  norm_num [B_good,hq]

theorem d4_two_simple : IsSimpleGroup (DPlus 4 (ZMod 2)) :=
  DPlus_simple 4 (by decide)
end Atlas.Orthogonal.Checks
