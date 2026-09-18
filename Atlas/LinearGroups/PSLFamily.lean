/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.LinearGroups.PSLExceptions

/-! # The uniform simplicity theorem with its exact exceptional set -/

namespace Atlas
open scoped MatrixGroups

variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
theorem psl_simple_rank_two (hF : 4 ≤ Nat.card F) : IsSimpleGroup (PSL(2, F)) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF

theorem psl_nonabelian_rank_two (hF : 4 ≤ Nat.card F) : ¬ IsMulCommutative (PSL(2, F)) := by
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ) (k := 2) (by decide)
    (by rw [Nat.card_units]; omega)
  have ha' : (a : F) ^ 2 ≠ 1 := fun h ↦ ha (Units.ext (by simpa using h))
  let : Group.IsPerfect (SL(2, F)) := ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero a) ha'⟩
  let : Group.IsPerfect (PSL(2, F)) := inferInstance
  exact Group.IsPerfect.not_isMulCommutative _

theorem psl_simple_iff (n : ℕ) (hn : 2 ≤ n) :
    IsSimpleGroup (PSL(n, F)) ↔
      (n, Nat.card F) ≠ (2, 2) ∧ (n, Nat.card F) ≠ (2, 3) := by
  constructor
  · intro hs
    constructor
    · intro he
      have h : n = 2 := congrArg Prod.fst he
      have hq : Nat.card F = 2 := congrArg Prod.snd he
      subst n
      exact psl_two_two_not_simple hq hs
    · intro he
      have h : n = 2 := congrArg Prod.fst he
      have hq : Nat.card F = 3 := congrArg Prod.snd he
      subst n
      exact psl_two_three_not_simple hq hs
  · rintro ⟨h2, h3⟩
    by_cases h : n = 2
    · subst n
      have hq2 : Nat.card F ≠ 2 := fun hq ↦ h2 (congrArg (fun q : ℕ ↦ (2, q)) hq)
      have hq3 : Nat.card F ≠ 3 := fun hq ↦ h3 (congrArg (fun q : ℕ ↦ (2, q)) hq)
      have hq : 1 < Nat.card F := Finite.one_lt_card
      exact psl_simple_rank_two (by omega)
    · exact psl_simple_high_rank n (by omega)

theorem psl_nonabelian_simple (n : ℕ) (hn : 2 ≤ n)
    (h2 : (n, Nat.card F) ≠ (2, 2)) (h3 : (n, Nat.card F) ≠ (2, 3)) :
    IsSimpleGroup (PSL(n, F)) ∧ ¬ IsMulCommutative (PSL(n, F)) := by
  refine ⟨(psl_simple_iff n hn).mpr ⟨h2, h3⟩, ?_⟩
  by_cases h : n = 2
  · subst n
    have hq2 : Nat.card F ≠ 2 := fun hq ↦ h2 (congrArg (fun q : ℕ ↦ (2, q)) hq)
    have hq3 : Nat.card F ≠ 3 := fun hq ↦ h3 (congrArg (fun q : ℕ ↦ (2, q)) hq)
    have hq : 1 < Nat.card F := Finite.one_lt_card
    exact psl_nonabelian_rank_two (by omega)
  · exact psl_nonabelian_high_rank n (by omega)

end Atlas
