import Atlas.LinearGroups.Orthogonal.B2ExteriorSymplectic
import Atlas.LinearGroups.Orthogonal.IntrinsicStandard
import Atlas.LinearGroups.Symplectic.Perfectness

/-! # The actual exterior-square image lies in the intrinsic odd B₂ kernel -/
noncomputable section
namespace Atlas.Orthogonal.B2Exterior
variable {F : Type*} [Field F] [Finite F]

theorem toOrthogonal_mem_elementary (h2 : (2 : F) ≠ 0) (g : Atlas.Symplectic.Sp 2 F) :
    toOrthogonal g ∈ elementarySubgroup (formB 2 F) := by
  have hcard : Nat.card F ≠ 2 := by
    intro hc
    letI := Fintype.ofFinite F
    have hc' : Fintype.card F = 2 := by simpa only [Nat.card_eq_fintype_card] using hc
    letI : CharP F 2 := charP_of_card_eq_prime hc'
    exact h2 CharTwo.two_eq_zero
  letI := Atlas.Symplectic.perfect_of_good (F := F)
    (show Atlas.Symplectic.Good 2 (Nat.card F) from Or.inr ⟨le_rfl, by
      intro h
      exact hcard (congrArg Prod.snd h)⟩)
  letI := Group.IsPerfect.range (toOrthogonal (F := F))
  rw [elementaryB_eq_commutator 0 h2]
  have hr : toOrthogonal g ∈ (toOrthogonal (F := F)).range := ⟨g, rfl⟩
  rw [← Subgroup.commutator_eq_self (H := (toOrthogonal (F := F)).range)] at hr
  exact (Subgroup.commutator_mono (show (toOrthogonal (F := F)).range ≤ ⊤ from le_top)
    (show (toOrthogonal (F := F)).range ≤ ⊤ from le_top)) hr

def toElementary (h2 : (2 : F) ≠ 0) :
    Atlas.Symplectic.Sp 2 F →* elementarySubgroup (formB 2 F) :=
  toOrthogonal.codRestrict _ (toOrthogonal_mem_elementary h2)

theorem toElementary_coe (h2 : (2 : F) ≠ 0) (g : Atlas.Symplectic.Sp 2 F) :
    (toElementary h2 g).val = toOrthogonal g := rfl
end Atlas.Orthogonal.B2Exterior
