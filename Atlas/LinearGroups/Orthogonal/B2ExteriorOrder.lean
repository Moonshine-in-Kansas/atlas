import Atlas.LinearGroups.Orthogonal.IntrinsicStandard
import Atlas.LinearGroups.Symplectic.ProjectiveOrder
import Atlas.Algebra.FiniteFieldSignSquares

/-! # Independent order equality for the actual B₂ and projective C₂ carriers -/
noncomputable section
namespace Atlas.Orthogonal.B2Exterior
variable {F : Type*} [Field F] [Finite F]

theorem card_psp_eq_elementary (h2 : (2 : F) ≠ 0) :
    Nat.card (Atlas.Symplectic.PSp 2 F) = Nat.card (elementarySubgroup (formB 2 F)) := by
  have ho := Atlas.odd_card_mod_two h2
  have hd : 2 ∣ Nat.card F - 1 := by omega
  have hg : Nat.gcd 2 (Nat.card F - 1) = 2 := Nat.gcd_eq_left hd
  rw [Atlas.Symplectic.card_psp (by decide : 0 < 2), hg, card_elementaryB 0 h2]
  rfl
end Atlas.Orthogonal.B2Exterior
