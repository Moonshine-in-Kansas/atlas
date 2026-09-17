import Atlas.LinearGroups.Orthogonal.DStructureAllChar
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Small split-D order regressions obtained from uniform formulas -/
namespace Atlas.Orthogonal.Checks

/-- The actual ternary rank-four projective quadratic group. -/
theorem d4_three_order :
    Nat.card (ProjectiveElementary (formD 4 (ZMod 3))) = 4952179814400 := by
  have h := card_projectiveD_all_char (F := ZMod 3) 1
  norm_num [Finset.prod_range_succ, Nat.card_eq_fintype_card] at h ⊢
  exact h

/-- A genuine four-element field, rather than the nonfield ZMod 4. -/
theorem d4_four_order :
    Nat.card (ProjectiveElementary (formD 4 (GaloisField 2 2))) = 67010895544320000 := by
  have hq : Nat.card (GaloisField 2 2) = 4 := by
    simpa using GaloisField.card 2 2 (by decide)
  have h := card_projectiveD_all_char (F := GaloisField 2 2) 1
  rw [hq] at h
  norm_num [Finset.prod_range_succ] at h
  exact h
end Atlas.Orthogonal.Checks
