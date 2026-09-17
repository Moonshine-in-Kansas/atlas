import Atlas.Conway.EisensteinNineHexadOrbitExclusions
import Atlas.Conway.EisensteinElevenOrbits
import Atlas.Conway.EisensteinConstantBalancedSeparation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

theorem eisensteinUnitSuborbit_subset (i : Fin 13)
    (hi : i=5 ∨ i=6 ∨ i=7 ∨ i=9 ∨ i=10 ∨ i=11) :
    eisensteinSuborbitFrames i ⊆ eisensteinUnitResidueFrames := by
  intro F hF
  apply (eisensteinUnitResidueFrames_mem F).mpr
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inl hF
  · exact Or.inr (Or.inl ⟨false,hF⟩)
  · exact Or.inr (Or.inl ⟨true,hF⟩)
  · exact Or.inr (Or.inr ⟨0,hF⟩)
  · exact Or.inr (Or.inr ⟨1,hF⟩)
  · exact Or.inr (Or.inr ⟨2,hF⟩)

theorem eisensteinSubdegree_divisible243_indices (i : Fin 13) (h3 : i≠3) (h4 : i≠4)
    (h12 : i≠12) (hd : 243 ∣ eisensteinSubdegree i) :
    i=5 ∨ i=6 ∨ i=7 ∨ i=9 ∨ i=10 ∨ i=11 := by
  have h : ∀ j : Fin 13,j≠3 → j≠4 → j≠12 → 243 ∣ eisensteinSubdegree j →
      j=5 ∨ j=6 ∨ j=7 ∨ j=9 ∨ j=10 ∨ j=11 := by decide +kernel
  exact h i h3 h4 h12 hd

/-- Canonical constant norm-nine families avoid all eleven previously proved
local orbits. No full-local invariance of the2673 families is assumed. -/
theorem eisensteinNineHexadFamily_other_disjoint (b : ZMod 3) (hb : b≠0)
    (i : Fin 13) (h3 : i≠3) (h4 : i≠4) :
    Disjoint (↑(eisensteinNineHexadFamily b hb) : Set EisensteinFrame) (eisensteinSuborbitFrames i) := by
  by_cases hd : 243 ∣ eisensteinSubdegree i
  · by_cases h12 : i=12
    · subst i
      apply Set.disjoint_left.mpr
      intro F hF hG
      exact Finset.disjoint_left.mp (eisensteinNineHexad_balancedNine_disjoint b hb) hF hG
    · have hi : i=5 ∨ i=6 ∨ i=7 ∨ i=9 ∨ i=10 ∨ i=11 := eisensteinSubdegree_divisible243_indices i h3 h4 h12 hd
      exact (eisensteinNineHexadFamily_unit_disjoint b hb).mono_right (eisensteinUnitSuborbit_subset i hi)
  · obtain ⟨F,hF⟩ := eisensteinElevenSuborbit_orbit i h3 h4
    rw [hF]
    apply eisensteinNineHexadFamily_disjoint_local_orbit b hb F
    rw [← hF,eisensteinSuborbitFrames_card]
    exact hd

end Atlas.Conway
