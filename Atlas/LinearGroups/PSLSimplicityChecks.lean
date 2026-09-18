/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.LinearGroups.PSLFamily

/-! # Regression corollaries of the exact family theorem -/

namespace Atlas
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]

theorem psl_two_two_check (hF : Nat.card F = 2) :
    ¬ IsSimpleGroup (PSL(2, F)) ∧ Nat.card (PSL(2, F)) = 6 := by
  refine ⟨?_, card_psl_two_two hF⟩
  intro hs
  exact ((psl_simple_iff 2 (by decide)).mp hs).1 (congrArg (fun q : ℕ ↦ (2, q)) hF)

theorem psl_two_three_check (hF : Nat.card F = 3) :
    ¬ IsSimpleGroup (PSL(2, F)) ∧ Nat.card (PSL(2, F)) = 12 := by
  refine ⟨?_, card_psl_two_three hF⟩
  intro hs
  exact ((psl_simple_iff 2 (by decide)).mp hs).2 (congrArg (fun q : ℕ ↦ (2, q)) hF)

theorem psl_two_four_check (hF : Nat.card F = 4) :
    IsSimpleGroup (PSL(2, F)) ∧ ¬ IsMulCommutative (PSL(2, F)) ∧
      Nat.card (PSL(2, F)) = 60 := by
  have h := psl_nonabelian_simple (F := F) 2 (by decide)
    (by intro e; have h := congrArg Prod.snd e; rw [hF] at h; norm_num at h)
    (by intro e; have h := congrArg Prod.snd e; rw [hF] at h; norm_num at h)
  exact ⟨h.1, h.2, card_psl_two_four hF⟩

theorem psl_two_five_check (hF : Nat.card F = 5) :
    IsSimpleGroup (PSL(2, F)) ∧ ¬ IsMulCommutative (PSL(2, F)) ∧
      Nat.card (PSL(2, F)) = 60 := by
  have h := psl_nonabelian_simple (F := F) 2 (by decide)
    (by intro e; have h := congrArg Prod.snd e; rw [hF] at h; norm_num at h)
    (by intro e; have h := congrArg Prod.snd e; rw [hF] at h; norm_num at h)
  exact ⟨h.1, h.2, card_psl_two_five hF⟩

theorem psl_three_two_check (hF : Nat.card F = 2) :
    IsSimpleGroup (PSL(3, F)) ∧ ¬ IsMulCommutative (PSL(3, F)) ∧
      Nat.card (PSL(3, F)) = 168 := by
  have h := psl_nonabelian_simple (F := F) 3 (by decide)
    (by intro e; have h := congrArg Prod.fst e; norm_num at h)
    (by intro e; have h := congrArg Prod.fst e; norm_num at h)
  exact ⟨h.1, h.2, card_psl_three_two hF⟩

theorem psl_three_three_check (hF : Nat.card F = 3) :
    IsSimpleGroup (PSL(3, F)) ∧ ¬ IsMulCommutative (PSL(3, F)) ∧
      Nat.card (PSL(3, F)) = 5616 := by
  have h := psl_nonabelian_simple (F := F) 3 (by decide)
    (by intro e; have h := congrArg Prod.fst e; norm_num at h)
    (by intro e; have h := congrArg Prod.fst e; norm_num at h)
  refine ⟨h.1, h.2, ?_⟩
  rw [card_psl_product, hF]
  norm_num [Fin.prod_univ_succ]

end Atlas
