import Atlas.Conway.EisensteinNineHexadTransitive
import Atlas.Conway.EisensteinElevenOrbits

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices MulAction
open scoped BigOperators
attribute [local irreducible] eisensteinNineHexadFamily

theorem eisensteinSuborbitFrames_orbit (i : Fin 13) :
    ∃ F : EisensteinFrame,
      eisensteinSuborbitFrames i = orbit eisensteinCoordinateFrameStabilizer F := by
  by_cases h3 : i=3
  · subst i
    obtain ⟨F,hF⟩ := Finset.card_pos.mp
      (show 0<(eisensteinNineHexadFamily 1 (by decide)).card by
        rw [eisensteinNineHexadFamily_card]; decide)
    exact ⟨F,(eisensteinNineHexadFamily_orbit 1 (by decide) F hF).symm⟩
  by_cases h4 : i=4
  · subst i
    obtain ⟨F,hF⟩ := Finset.card_pos.mp
      (show 0<(eisensteinNineHexadFamily 2 (by decide)).card by
        rw [eisensteinNineHexadFamily_card]; decide)
    exact ⟨F,(eisensteinNineHexadFamily_orbit 2 (by decide) F hF).symm⟩
  exact eisensteinElevenSuborbit_orbit i h3 h4

theorem eisensteinSuborbitFrames_transitive (i : Fin 13) (F H : EisensteinFrame)
    (hF : F ∈ eisensteinSuborbitFrames i) (hH : H ∈ eisensteinSuborbitFrames i) :
    ∃ g : eisensteinCoordinateFrameStabilizer, g.val • F=H := by
  obtain ⟨X,hX⟩ := eisensteinSuborbitFrames_orbit i
  rw [hX] at hF hH
  obtain ⟨g,hg⟩ := hF
  obtain ⟨h,hh⟩ := hH
  change g.val • X = F at hg
  change h.val • X = H at hh
  refine ⟨h*g⁻¹,?_⟩
  change (h.val*g.val⁻¹) • F=H
  rw [mul_smul,← hg,inv_smul_smul,hh]

end Atlas.Conway
