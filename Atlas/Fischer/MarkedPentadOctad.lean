import Atlas.Fischer.MarkedBasicExtensionValues

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual unique Golay octad through a marked coordinate pentad. -/
def markedPentadOctad (S : Finset Omega) (hS : S.card = 5) : Octad :=
  ⟨(octad_steiner S hS).choose, (octad_steiner S hS).choose_spec.1.1⟩

theorem markedPentadOctad_contains (S : Finset Omega) (hS : S.card = 5) :
    S ⊆ (markedPentadOctad S hS).val :=
  (octad_steiner S hS).choose_spec.1.2

theorem markedPentadOctad_unique (S : Finset Omega) (hS : S.card = 5)
    (O : Octad) (hO : S ⊆ O.val) : O = markedPentadOctad S hS := by
  apply Subtype.ext
  exact (octad_steiner S hS).choose_spec.2 O.val ⟨O.prop,hO⟩

/-- A compatible octadic ray has exactly the pentad's unique octad support. -/
theorem markedPentadExtension_octadic (S : Finset Omega) (hS : S.card = 5)
    (t : OctadicRootParameter) :
    IsMarkedBasicExtension S (.inr (.inl t)) ↔ t.1 = markedPentadOctad S hS := by
  rw [markedBasicExtension_octadic]
  constructor
  · exact markedPentadOctad_unique S hS t.1
  · intro h
    rw [h]
    exact markedPentadOctad_contains S hS

/-- No duadic ray can commute with five different marked basic rays. -/
theorem markedPentadExtension_not_duadic (S : Finset Omega) (hS : S.card = 5)
    (t : DuadicRootParameter) : ¬ IsMarkedBasicExtension S (.inr (.inr t)) := by
  rw [markedBasicExtension_duadic]
  intro h
  have hc := Finset.card_le_card h
  have ht := t.1.prop
  omega

/-- The51 possible extensions are19 other basics and the32 characters over one octad. -/
theorem markedPentadExtension_classification (S : Finset Omega) (hS : S.card = 5)
    (t : ReflectingRootParameter) :
    IsMarkedBasicExtension S t ↔
      (∃ i : Omega, i ∉ S ∧ t = .inl i) ∨
      (∃ χ : OctadicCharacter (markedPentadOctad S hS),
        t = .inr (.inl ⟨markedPentadOctad S hS,χ⟩)) := by
  rcases t with i | (⟨O,χ⟩ | d)
  · simp [markedBasicExtension_basic]
  · rw [markedPentadExtension_octadic S hS]
    constructor
    · intro h
      change O=markedPentadOctad S hS at h
      subst O
      exact Or.inr ⟨χ,rfl⟩
    · rintro (⟨i,hi,h⟩ | ⟨ψ,h⟩)
      · cases h
      · exact congrArg Sigma.fst (Sum.inl.inj (Sum.inr.inj h))
  · constructor
    · exact fun h => (markedPentadExtension_not_duadic S hS d h).elim
    · rintro (⟨i,hi,h⟩ | ⟨χ,h⟩) <;> cases h

end Atlas.Fischer
