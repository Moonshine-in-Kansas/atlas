import Atlas.LinearGroups.Orthogonal.B2ExteriorKernelExact
import Atlas.LinearGroups.Orthogonal.B2ExteriorOrder
import Atlas.LinearGroups.Orthogonal.ProjectiveOddB

/-! # The actual odd B₂/C₂ comparison from the exterior-square homomorphism -/
noncomputable section
namespace Atlas.Orthogonal.B2Exterior
variable {F : Type*} [Field F] [Finite F]

def fromPSp (h2 : (2 : F) ≠ 0) :
    Atlas.Symplectic.PSp 2 F →* elementarySubgroup (formB 2 F) :=
  QuotientGroup.lift _ (toElementary h2) (by rw [toElementary_kernel h2])

theorem fromPSp_projection (h2 : (2 : F) ≠ 0) (g : Atlas.Symplectic.Sp 2 F) :
    fromPSp h2 (Atlas.Symplectic.projection g) = toElementary h2 g := rfl

theorem fromPSp_injective (h2 : (2 : F) ≠ 0) : Function.Injective (fromPSp h2) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (toElementary_kernel h2).symm

theorem fromPSp_bijective (h2 : (2 : F) ≠ 0) : Function.Bijective (fromPSp h2) :=
  (fromPSp_injective h2).bijective_of_nat_card_le (card_psp_eq_elementary h2).symm.le

def pspEquivElementary (h2 : (2 : F) ≠ 0) :
    Atlas.Symplectic.PSp 2 F ≃* elementarySubgroup (formB 2 F) :=
  MulEquiv.ofBijective (fromPSp h2) (fromPSp_bijective h2)

def projectiveBEquivPSp (h2 : (2 : F) ≠ 0) :
    ProjectiveElementary (formB 2 F) ≃* Atlas.Symplectic.PSp 2 F :=
  (projectiveElementaryBEquiv 0 h2).trans (pspEquivElementary h2).symm

theorem toElementary_surjective (h2 : (2 : F) ≠ 0) : Function.Surjective (toElementary h2) := by
  intro g
  obtain ⟨p, hp⟩ := (fromPSp_bijective h2).surjective g
  obtain ⟨x, rfl⟩ := Atlas.Symplectic.projection_surjective p
  exact ⟨x, hp⟩

theorem toOrthogonal_range (h2 : (2 : F) ≠ 0) :
    (toOrthogonal (F := F)).range = elementarySubgroup (formB 2 F) := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    exact toOrthogonal_mem_elementary h2 x
  · intro g hg
    obtain ⟨x, hx⟩ := toElementary_surjective h2 ⟨g, hg⟩
    exact ⟨x, congrArg Subtype.val hx⟩
end Atlas.Orthogonal.B2Exterior
