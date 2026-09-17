import Atlas.Conway.EisensteinFramePartition
import Atlas.Conway.EisensteinNineSignWitnesses

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local irreducible] eisensteinNineHexadFamily

/-- The intrinsic sign splits the saturated5346-frame complement into its two
actual invariant2673-frame families. -/
theorem eisensteinNineHexadFamily_preserved (b : ZMod 3) (hb : b≠0)
    (g : eisensteinCoordinateFrameStabilizer) (F : EisensteinFrame)
    (hF : F ∈ eisensteinNineHexadFamily b hb) :
    g.val • F ∈ eisensteinNineHexadFamily b hb := by
  have hsign := eisensteinNineSignFrame_preserved b g F (eisensteinNineHexadFamily_sign b hb F hF)
  have hcases : b=1 ∨ b=2 := (by decide : ∀ a : ZMod 3,a≠0 → a=1 ∨ a=2) b hb
  have hu : F ∈ eisensteinNineHexadFamily 1 (by decide) ∨
      F ∈ eisensteinNineHexadFamily 2 (by decide) := by
    rcases hcases with h|h
    · subst b; exact Or.inl hF
    · subst b; exact Or.inr hF
  rcases eisensteinNineHexadUnion_invariant g F hu with h|h
  · have he := eisensteinNineSignFrame_unique b 1 (g.val • F) hsign
      (eisensteinNineHexadFamily_sign 1 (by decide) _ h)
    subst b
    exact h
  · have he := eisensteinNineSignFrame_unique b 2 (g.val • F) hsign
      (eisensteinNineHexadFamily_sign 2 (by decide) _ h)
    subst b
    exact h

end Atlas.Conway
