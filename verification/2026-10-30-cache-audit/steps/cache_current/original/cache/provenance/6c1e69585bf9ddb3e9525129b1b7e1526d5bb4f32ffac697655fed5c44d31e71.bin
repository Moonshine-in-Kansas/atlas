/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! Faithful primitive actions and point-stabilizer restriction. -/

namespace Atlas.GroupTheory

variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]

/-- A nontrivial normal subgroup in a faithful primitive action is transitive. -/
theorem normal_pretransitive [MulAction.IsPreprimitive G X]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : MulAction.IsPretransitive N X := by
  apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
  intro h
  apply hN
  apply le_antisymm _ bot_le
  intro n hn
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := X)
  intro x
  have hx : x ∈ MulAction.fixedPoints N X := by rw [h]; trivial
  exact (MulAction.mem_fixedPoints.mp hx ⟨n,hn⟩).trans (one_smul G x).symm

/-- Restriction to the complement of a fixed point retains faithfulness. -/
theorem stabilizer_complement_faithful (a : X) :
    FaithfulSMul (MulAction.stabilizer G a) (SubMulAction.ofStabilizer G a) where
  eq_of_smul_eq_smul {g h} he := by
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := X)
    intro x
    by_cases hx : x = a
    · subst x
      exact g.property.trans h.property.symm
    · exact congrArg Subtype.val (he ⟨x,hx⟩)


end Atlas.GroupTheory
