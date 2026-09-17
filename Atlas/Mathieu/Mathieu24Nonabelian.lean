/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.Mathieu24Alternating

noncomputable section
namespace Atlas.Codes

theorem hexZ_local_fixed : ∀ (i : HexIndex) (u : K),
    (if i.2 = 0 then localKappa else localKappa⁻¹) u = u → u = 0 := by decide

theorem hexZ_moves_nonzero (h : hexacode) (hn : h ≠ 0) : hexAction hexZ h ≠ h := by
  intro he
  apply hn
  apply Subtype.ext
  funext i
  have hi := congrArg (fun w : hexacode => w.val i) he
  exact hexZ_local_fixed i (h.val i) hi

/-- The local order-three section does not commute with any nonzero translation. -/
theorem hexZ_translation_noncommute (h : hexacode) (hn : h ≠ 0) :
    (sextetSection hexZ).val * (sextetTranslation (Multiplicative.ofAdd h)).val ≠
      (sextetTranslation (Multiplicative.ofAdd h)).val * (sextetSection hexZ).val := by
  intro he
  have hs : sextetSection hexZ * sextetTranslation (Multiplicative.ofAdd h) =
      sextetTranslation (Multiplicative.ofAdd h) * sextetSection hexZ := Subtype.ext he
  have hc : sextetSection hexZ * sextetTranslation (Multiplicative.ofAdd h) * (sextetSection hexZ)⁻¹ =
      sextetTranslation (Multiplicative.ofAdd h) := by
    rw [hs,mul_assoc,mul_inv_cancel,mul_one]
  rw [sextet_translation_conjugation] at hc
  have hh := sextetTranslation_injective hc
  exact hexZ_moves_nonzero h hn (congrArg Multiplicative.toAdd hh)

theorem mathieu24_noncommuting_pair : ∃ g h : Mathieu24CodeModel, g*h ≠ h*g := by
  obtain ⟨h,hh⟩ := hexCoordinate_surjective (0,0) a
  have hn : h ≠ 0 := by
    intro he
    rw [he,map_zero] at hh
    exact (by decide : (0 : K) ≠ a) hh
  exact ⟨(sextetSection hexZ).val,(sextetTranslation (Multiplicative.ofAdd h)).val,
    hexZ_translation_noncommute h hn⟩

end Atlas.Codes
