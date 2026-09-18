/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.LinearGroups.ProjectiveSpecialLinear
import Mathlib.Tactic.NormNum

/-!
# Small-order regression checks

These specialize the uniform family theorem to a field of the stated order.
Only the resulting natural-number arithmetic is evaluated; no group elements
are enumerated. In particular the order-four field is not confused with Z/4Z.
-/

namespace Atlas

open scoped MatrixGroups

variable {F : Type*} [Field F] [Finite F]

theorem card_psl_two_two (hF : Nat.card F = 2) : Nat.card (PSL(2, F)) = 6 := by
  rw [card_psl_product, hF]
  norm_num [Fin.prod_univ_succ]

theorem card_psl_two_three (hF : Nat.card F = 3) : Nat.card (PSL(2, F)) = 12 := by
  rw [card_psl_product, hF]
  norm_num [Fin.prod_univ_succ]

theorem card_psl_two_four (hF : Nat.card F = 4) : Nat.card (PSL(2, F)) = 60 := by
  rw [card_psl_product, hF]
  norm_num [Fin.prod_univ_succ]

theorem card_psl_two_five (hF : Nat.card F = 5) : Nat.card (PSL(2, F)) = 60 := by
  rw [card_psl_product, hF]
  norm_num [Fin.prod_univ_succ]

theorem card_psl_three_two (hF : Nat.card F = 2) : Nat.card (PSL(3, F)) = 168 := by
  rw [card_psl_product, hF]
  norm_num [Fin.prod_univ_succ]

end Atlas
