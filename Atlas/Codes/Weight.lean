/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Codes.Alphabets

namespace Atlas.Codes
open scoped BigOperators

theorem bit_cases (x : Bit) : x = 0 ∨ x = 1 := by revert x; decide

theorem hammingNorm_prod {ι κ A : Type*} [Fintype ι] [Fintype κ] [Zero A]
    [DecidableEq A] (w : ι × κ → A) :
    hammingNorm w = ∑ i, hammingNorm (fun j => w (i, j)) := by
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_prod_type]

theorem bit_sum_eq_weight {ι : Type*} [Fintype ι] (w : ι → Bit) :
    ∑ i, w i = (hammingNorm w : Bit) := by
  classical
  simp only [hammingNorm, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases bit_cases (w i) with h | h <;> simp [h]

theorem even_weight_iff {ι : Type*} [Fintype ι] (w : ι → Bit) :
    Even (hammingNorm w) ↔ ∑ i, w i = 0 := by
  rw [bit_sum_eq_weight, ZMod.natCast_eq_zero_iff_even]

theorem positive_even_weight {ι A : Type*} [Fintype ι] [Zero A] [DecidableEq A]
    (w : ι → A) (hw : w ≠ 0) (he : Even (hammingNorm w)) : 2 ≤ hammingNorm w := by
  have hp := hammingNorm_pos_iff.mpr hw
  obtain ⟨k, hk⟩ := he
  omega

theorem hammingNorm_eq_sum {ι A : Type*} [Fintype ι] [Zero A] [DecidableEq A]
    (w : ι → A) : hammingNorm w = ∑ i, if w i = 0 then 0 else 1 := by
  classical
  simp [hammingNorm, Finset.card_filter]

end Atlas.Codes
