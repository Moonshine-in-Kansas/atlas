import Atlas.Rudvalis.IntrinsicConfigurations

namespace Atlas.Rudvalis

theorem isQuartet_contains_couple (Q : Set MinimalCross) (hQ : IsQuartet Q) :
    ∃c : Set MinimalCross,IsCouple c ∧ c⊆Q := by
  obtain ⟨a,b,c,d,hab,_,_,_,_,_,he⟩ := Set.ncard_eq_four.mp hQ.1
  have ha : a∈Q := by rw [he]; exact Or.inl rfl
  have hb : b∈Q := by rw [he]; exact Or.inr (Or.inl rfl)
  have hs : ({a,b} : Set MinimalCross)⊆Q := by
    rintro z (rfl|rfl)
    · exact ha
    · exact hb
  refine ⟨{a,b},⟨Set.ncard_pair hab,?_⟩,hs⟩
  intro x hx y hy hxy
  exact hQ.2.1 (hs hx) (hs hy) hxy

end Atlas.Rudvalis
