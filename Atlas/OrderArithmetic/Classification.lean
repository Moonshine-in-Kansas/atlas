import Atlas.OrderArithmetic.LieDominance
import Atlas.OrderArithmetic.RankOneDominantComparison
import Atlas.OrderArithmetic.DominantCharacteristicCollision
import Atlas.OrderArithmetic.IsolatedCollision

namespace Atlas.OrderArithmetic

/-- Unbounded equality classification for all admissible ordinary Lie formulas. -/
theorem lie_equal_order_collision {x y : RawEntry}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (he : order x = order y) : Collision x y := by
  by_cases hx33 : x = .unitary 3 3
  · subst x; exact unitary_three_three_equal_order_collision hy hly he
  by_cases hy33 : y = .unitary 3 3
  · subst y; exact collision_symm (unitary_three_three_equal_order_collision hx hlx he.symm)
  by_cases hx42 : x = .unitary 4 2
  · subst x; exact unitary_four_two_equal_order_collision hy hly he
  by_cases hy42 : y = .unitary 4 2
  · subst y; exact collision_symm (unitary_four_two_equal_order_collision hx hlx he.symm)
  obtain ⟨p, f, hp, hf, hqx⟩ := lie_field_primePower hx hlx
  obtain ⟨r, g, hr, hg, hqy⟩ := lie_field_primePower hy hly
  by_cases hx2 : ∃ q, x = .linear 2 q
  · obtain ⟨q, rfl⟩ := hx2
    by_cases hy2 : ∃ s, y = .linear 2 s
    · obtain ⟨s, rfl⟩ := hy2
      exact linear_two_equal_order_collision hx hy hp hr hf hg hqx hqy he
    · have hny : ∀ s, y ≠ .linear 2 s := fun s hs => hy2 ⟨s, hs⟩
      exact linear_two_collision_of_dominant_competitor hx hy hly hp hr hf hg hqx hqy
        (fun l hl hlq => lie_cross_contribution_lt hy hly hny hy33 hy42 hl hlq) he
  have hnx : ∀ q, x ≠ .linear 2 q := fun q hq => hx2 ⟨q, hq⟩
  by_cases hy2 : ∃ s, y = .linear 2 s
  · obtain ⟨s, rfl⟩ := hy2
    exact collision_symm (linear_two_collision_of_dominant_competitor hy hx hlx hr hp hg hf hqy hqx
      (fun l hl hlq => lie_cross_contribution_lt hx hlx hnx hx33 hx42 hl hlq) he.symm)
  have hny : ∀ s, y ≠ .linear 2 s := fun s hs => hy2 ⟨s, hs⟩
  exact collision_of_dominant_characteristics hx hy hlx hly hp hr hf hg hqx hqy
    (fun l hl hlq => lie_cross_contribution_lt hx hlx hnx hx33 hx42 hl hlq)
    (fun l hl hlq => lie_cross_contribution_lt hy hly hny hy33 hy42 hl hlq) he

/-- Complete arithmetic classification, over all admissible labels and without
any bound on rank, field size, alternating degree or prime. This is a statement
about the literal integer formulas, not a recognition theorem for groups. -/
theorem catalogue_order_eq_iff {x y : RawEntry} (hx : Admissible x) (hy : Admissible y) :
    order x = order y ↔ Collision x y := by
  constructor
  · intro he
    by_cases hlx : IsLie x
    · by_cases hly : IsLie y
      · exact lie_equal_order_collision hx hy hlx hly he
      · exact (catalogue_order_eq_iff_elementary hx hy (Or.inr hly)).mp he
    · exact (catalogue_order_eq_iff_elementary hx hy (Or.inl hlx)).mp he
  · exact collision_order

/-- Different normalized labels outside the stated exceptions have unequal orders. -/
theorem catalogue_orders_distinct {x y : RawEntry} (hx : Admissible x) (hy : Admissible y)
    (hn : normalize x ≠ normalize y) (he : ¬ Exceptional (normalize x) (normalize y)) :
    order x ≠ order y := by
  intro h
  rcases (catalogue_order_eq_iff hx hy).mp h with h | h
  · exact hn h
  · exact he h

/-- Inequality in the absence of a syntactic collision. -/
theorem catalogue_order_ne {x y : RawEntry} (hx : Admissible x) (hy : Admissible y)
    (h : ¬ Collision x y) : order x ≠ order y := by
  exact fun he => h ((catalogue_order_eq_iff hx hy).mp he)

end Atlas.OrderArithmetic
