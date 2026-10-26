import Atlas.GroupTheory.RankThreePrimitive

/-! A primitive-action criterion using one stabilizer orbit and an explicit move
out of the complementary relation. No subdegree counts or maximality premise. -/
namespace Atlas.GroupTheory
open MulAction
variable {G X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]

theorem primitive_of_nonrelated_orbit_and_moves (a : X) (R : X → X → Prop)
    (hSymm : Symmetric R)
    (hOrbit : ∀ x y z, ¬ R x y → ¬ R x z → ∃ g : stabilizer G x, g • y = z)
    (hBridge : ∀ x y, x ≠ y → R x y → ∃ z, ¬ R x z ∧ ¬ R y z)
    (hMove : ∀ x y, x ≠ y → R x y → ∃ g : stabilizer G y, ¬ R x (g • x)) :
    IsPreprimitive G X := by
  classical
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  by_cases hs : ∀ x ∈ B, x = a
  · exact Or.inl (fun x hx y hy => (hs x hx).trans (hs y hy).symm)
  · push_neg at hs
    obtain ⟨b,hb,hba⟩ := hs
    have hn : ∃ c ∈ B, ¬ R a c := by
      by_cases hab : R a b
      · obtain ⟨g,hg⟩ := hMove a b (Ne.symm hba) hab
        refine ⟨g • a, ?_, hg⟩
        exact block_contains_stabilizer_transport hB hb ha ⟨g,rfl⟩
      · exact ⟨b,hb,hab⟩
    obtain ⟨c,hc,hac⟩ := hn
    have hAll (x : X) (hax : ¬ R a x) : x ∈ B :=
      block_contains_stabilizer_transport hB ha hc (hOrbit a c x hac hax)
    right
    apply Set.eq_univ_of_forall
    intro r
    by_cases hra : r = a
    · simpa [hra] using ha
    by_cases har : R a r
    · obtain ⟨z,haz,hrz⟩ := hBridge a r (Ne.symm hra) har
      exact block_contains_stabilizer_transport hB (hAll z haz) ha
        (hOrbit z a r (fun h => haz (hSymm h)) (fun h => hrz (hSymm h)))
    · exact hAll r har
end Atlas.GroupTheory
