import Atlas.LinearGroups.Orthogonal.BAllRanks
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Required rank-three B order regressions

These are specializations of the uniform order proof on the actual public model.
The four-element coefficient field is a Galois field, not ZMod 4.
-/
namespace Atlas.Orthogonal.Checks

theorem b3_two_order : Nat.card (B 3 (ZMod 2)) = 1451520 := by
  rw [B_card_all_rank 3 (by decide)]
  norm_num [B_order,B_order_numerator,B_order_denominator,Nat.card_zmod,Finset.prod_range_succ]

theorem b3_three_order : Nat.card (B 3 (ZMod 3)) = 4585351680 := by
  rw [B_card_all_rank 3 (by decide)]
  norm_num [B_order,B_order_numerator,B_order_denominator,Nat.card_zmod,Finset.prod_range_succ]

theorem b3_four_order : Nat.card (B 3 (GaloisField 2 2)) = 4106059776000 := by
  have hq : Nat.card (GaloisField 2 2) = 4 := by
    simpa using GaloisField.card 2 2 (by decide)
  rw [B_card_all_rank 3 (by decide),hq]
  norm_num [B_order,B_order_numerator,B_order_denominator,Finset.prod_range_succ]
end Atlas.Orthogonal.Checks
