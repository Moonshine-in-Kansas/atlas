/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.LinearGroups.PSLSimplicity
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-! # The two nonsimple projective special linear groups -/

namespace Atlas
open scoped MatrixGroups LinearAlgebra.Projectivization

private theorem simple_faithful_action_to_alternating
    (G X : Type*) [Group G] [IsSimpleGroup G] [Finite G]
    [Fintype X] [DecidableEq X] [MulAction G X] [FaithfulSMul G X]
    (hc : 2 < Nat.card G) :
    ∃ f : G →* alternatingGroup X, Function.Injective f := by
  let p := MulAction.toPermHom G X
  let s := Equiv.Perm.sign.comp p
  have hs : s.ker = ⊤ := by
    rcases s.normal_ker.eq_bot_or_eq_top with h | h
    · have hi := s.ker_eq_bot_iff.mp h
      have hh := Nat.card_le_card_of_injective s hi
      have hu : Nat.card ℤˣ = 2 := by simp [Nat.card_eq_fintype_card]
      rw [hu] at hh
      omega
    · exact h
  let f : G →* alternatingGroup X := p.codRestrict _ fun g ↦ by
    change s g = 1
    exact MonoidHom.mem_ker.mp (hs ▸ Subgroup.mem_top g)
  refine ⟨f, ?_⟩
  intro a b hab
  apply (MulAction.toPerm_injective (β := X))
  exact congrArg Subtype.val hab

theorem psl_two_two_not_simple {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : ¬ IsSimpleGroup (PSL(2, F)) := by
  classical
  intro hs
  let X := ℙ F (Fin 2 → F)
  let : Fintype X := Fintype.ofFinite X
  have hx : Nat.card X = 3 := by
    change Nat.card (ℙ F (Fin 2 → F)) = _
    rw [card_projectiveSpace, hF]
    norm_num
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨f, hf⟩ := simple_faithful_action_to_alternating (PSL(2, F)) X
    (by rw [card_psl_two_two hF]; omega)
  have h := Nat.card_le_card_of_injective f hf
  rw [card_psl_two_two hF, nat_card_alternatingGroup, hx] at h
  norm_num [Nat.factorial] at h

theorem psl_two_three_not_simple {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3) : ¬ IsSimpleGroup (PSL(2, F)) := by
  classical
  intro hs
  let X := ℙ F (Fin 2 → F)
  let : Fintype X := Fintype.ofFinite X
  have hx : Nat.card X = 4 := by
    change Nat.card (ℙ F (Fin 2 → F)) = _
    rw [card_projectiveSpace, hF]
    norm_num
  obtain ⟨f, hf⟩ := simple_faithful_action_to_alternating (PSL(2, F)) X
    (by rw [card_psl_two_three hF]; omega)
  have hcard : Nat.card (PSL(2, F)) = Nat.card (alternatingGroup X) := by
    rw [card_psl_two_three hF, alternatingGroup.card_of_card_eq_four hx]
  let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩)
  let : IsSimpleGroup (alternatingGroup X) := e.symm.isSimpleGroup
  have hk := alternatingGroup.kleinFour_card_of_card_eq_four hx
  rcases (alternatingGroup.normal_kleinFour hx).eq_bot_or_eq_top with h | h
  · rw [h] at hk
    norm_num [Nat.factorial] at hk
  · rw [h] at hk
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv,
      alternatingGroup.card_of_card_eq_four hx] at hk
    norm_num at hk

end Atlas
