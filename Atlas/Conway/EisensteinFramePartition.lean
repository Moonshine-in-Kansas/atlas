import Atlas.Conway.EisensteinNineOtherDisjoint
import Atlas.Conway.EisensteinRepeatedSuborbits
import Atlas.GroupTheory.OrbitCardDisjoint
import Atlas.GroupTheory.FiniteFamilyExhaustion

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices
open scoped BigOperators
attribute [local irreducible] eisensteinNineHexadFamily

theorem eisensteinSuborbitFrames_pairwise :
    Pairwise (fun i j => Disjoint (eisensteinSuborbitFrames i) (eisensteinSuborbitFrames j)) := by
  intro i j hij
  by_cases hd : eisensteinSubdegree i=eisensteinSubdegree j
  · exact eisensteinSuborbitFrames_repeated_disjoint i j hij hd
  · by_cases hi3 : i=3
    · subst i
      have hj3 : j≠3 := Ne.symm hij
      have hj4 : j≠4 := by intro h; subst j; exact hd rfl
      exact eisensteinNineHexadFamily_other_disjoint 1 (by decide) j hj3 hj4
    by_cases hi4 : i=4
    · subst i
      have hj4 : j≠4 := Ne.symm hij
      have hj3 : j≠3 := by intro h; subst j; exact hd rfl
      exact eisensteinNineHexadFamily_other_disjoint 2 (by decide) j hj3 hj4
    by_cases hj3 : j=3
    · subst j
      exact (eisensteinNineHexadFamily_other_disjoint 1 (by decide) i hi3 hi4).symm
    by_cases hj4 : j=4
    · subst j
      exact (eisensteinNineHexadFamily_other_disjoint 2 (by decide) i hi3 hi4).symm
    obtain ⟨F,hF⟩ := eisensteinElevenSuborbit_orbit i hi3 hi4
    obtain ⟨G,hG⟩ := eisensteinElevenSuborbit_orbit j hj3 hj4
    apply Atlas.GroupTheory.orbit_families_disjoint_of_card_ne _ _ F G hF hG
    simpa only [eisensteinSuborbitFrames_card] using hd

theorem eisensteinSuborbitFinset_pairwise :
    Pairwise (fun i j => Disjoint (eisensteinSuborbitFinset i) (eisensteinSuborbitFinset j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro F hF hG
  exact Set.disjoint_left.mp (eisensteinSuborbitFrames_pairwise hij)
    ((eisensteinSuborbitFinset_mem i F).mp hF) ((eisensteinSuborbitFinset_mem j F).mp hG)

/-- Exhaustion follows from disjointness and the independent intrinsic count.
It does not assume either constant norm-nine family is already a fullN-orbit. -/
theorem eisensteinSuborbitFrames_cover (F : EisensteinFrame) :
    ∃ i : Fin 13, F ∈ eisensteinSuborbitFrames i := by
  classical
  letI : Fintype EisensteinFrame := Fintype.ofFinite _
  obtain ⟨i,hi⟩ := Atlas.GroupTheory.finite_families_cover_of_card_sum
    eisensteinSuborbitFinset eisensteinSuborbitFinset_pairwise
    (by rw [eisensteinSuborbitFinset_sum,← Nat.card_eq_fintype_card,eisensteinFrame_card]) F
  exact ⟨i,(eisensteinSuborbitFinset_mem i F).mp hi⟩

theorem eisensteinFrame_other_or_nine (F : EisensteinFrame) :
    (∃ i : Fin 13, i≠3 ∧ i≠4 ∧ F ∈ eisensteinSuborbitFrames i) ∨
      F ∈ eisensteinNineHexadFamily 1 (by decide) ∨
      F ∈ eisensteinNineHexadFamily 2 (by decide) := by
  obtain ⟨i,hi⟩ := eisensteinSuborbitFrames_cover F
  by_cases h3 : i=3
  · subst i
    right; left
    exact hi
  by_cases h4 : i=4
  · subst i
    right; right
    exact hi
  exact Or.inl ⟨i,h3,h4,hi⟩

/-- The remaining5346 frames form an invariant union before its two signs
are separated into their individual local orbits. -/
theorem eisensteinNineHexadUnion_invariant (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame)
    (hF : F ∈ eisensteinNineHexadFamily 1 (by decide) ∨
      F ∈ eisensteinNineHexadFamily 2 (by decide)) :
    g.val • F ∈ eisensteinNineHexadFamily 1 (by decide) ∨
      g.val • F ∈ eisensteinNineHexadFamily 2 (by decide) := by
  rcases eisensteinFrame_other_or_nine (g.val • F) with ⟨i,hi3,hi4,hi⟩ | h
  · have hh := eisensteinElevenSuborbit_invariant i hi3 hi4 g⁻¹ (g.val • F) hi
    change g.val⁻¹ • (g.val • F) ∈ eisensteinSuborbitFrames i at hh
    rw [inv_smul_smul] at hh
    rcases hF with hF | hF
    · exact (Set.disjoint_left.mp
        (eisensteinNineHexadFamily_other_disjoint 1 (by decide) i hi3 hi4) hF hh).elim
    · exact (Set.disjoint_left.mp
        (eisensteinNineHexadFamily_other_disjoint 2 (by decide) i hi3 hi4) hF hh).elim
  · exact h

end Atlas.Conway
