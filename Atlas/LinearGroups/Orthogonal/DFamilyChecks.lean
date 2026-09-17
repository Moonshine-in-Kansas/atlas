import Atlas.LinearGroups.Orthogonal.ProjectiveDOrderAllChar

/-! # Small-field evaluations of the uniform split-D order theorem

These are consequences of the uniform proof, not replacements by enumeration.
-/
noncomputable section
namespace Atlas.Orthogonal

theorem card_projectiveD3_two :
    Nat.card (ProjectiveElementary (formD 3 (ZMod 2))) = 20160 := by
  have h := card_projectiveD_all_char (F := ZMod 2) 0
  norm_num [Finset.prod_range_succ] at h
  exact h

theorem card_projectiveD4_two :
    Nat.card (ProjectiveElementary (formD 4 (ZMod 2))) = 174182400 := by
  have h := card_projectiveD_all_char (F := ZMod 2) 1
  norm_num [Finset.prod_range_succ] at h
  exact h

end Atlas.Orthogonal
