import Atlas.Rudvalis.BinaryTranslations

/-! Radical rigidity for the alternating three-dimensional determinant forms. -/
namespace Atlas.Rudvalis

theorem polar_radical_iff (c v : E) (hc : c ≠ 0) :
    (∀ x : E, polar c v x = 0) ↔ v=0 ∨ v=c := by
  decide +kernel +revert

theorem polar_separates (v : E) (h : ∀ c x : E, polar c v x=0) : v=0 := by
  have he : ∀ v : E, (∀ c x : E, polar c v x=0) → v=0 := by decide +kernel
  exact he v h

theorem linearEquiv_preserving_polar_eq_one (A : E ≃ₗ[Bit] E)
    (h : ∀ c x y : E, polar c (A x) (A y)=polar c x y) : A=1 := by
  apply LinearEquiv.ext
  intro c
  change A c=c
  by_cases hc : c=0
  · subst c; exact map_zero A
  · have hr : ∀ y : E, polar c (A c) y=0 := by
      intro y
      obtain ⟨x,rfl⟩ := A.surjective y
      rw [h,quadratic_radical]
    rcases (polar_radical_iff c (A c) hc).mp hr with hz | he
    · exact (hc (A.injective (hz.trans (map_zero A).symm))).elim
    · exact he

end Atlas.Rudvalis
