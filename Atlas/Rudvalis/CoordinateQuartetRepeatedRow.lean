import Atlas.Rudvalis.CoordinateQuartetTwoRowClassification

namespace Atlas.Rudvalis

private theorem fourSet_reorder (a b c d : MinimalCross) :
    ({a,b,c,d} : Set MinimalCross)={b,a,d,c} := by ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto

/-- Any intrinsic coordinate quartet with a repeated row is already in the constructed family. -/
theorem coordinateQuartet_repeated_row (p q r : Point) (x y z t : E)
    (hxy : coordinateCross (p,x)≠coordinateCross (p,y))
    (hzt : coordinateCross (q,z)≠coordinateCross (r,t))
    (hQ : IsQuartet {coordinateCross (p,x),coordinateCross (p,y),coordinateCross (q,z),coordinateCross (r,t)}) :
    {coordinateCross (p,x),coordinateCross (p,y),coordinateCross (q,z),coordinateCross (r,t)}∈
      Set.range coordinateQuartetConstruction := by
  classical
  by_cases hpq : p=q
  · subst q
    by_cases hpr : p=r
    · subst r
      refine ⟨Sum.inl p,?_⟩
      change coordinateRowFrame p=_
      symm
      apply Set.eq_of_subset_of_ncard_le
      · intro c hc
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc
        rcases hc with rfl|rfl|rfl|rfl <;> exact ⟨_,rfl⟩
      · rw [hQ.1]
        change Nat.card (coordinateRowFrame p)≤4
        rw [coordinateRowFrame_card]
      · exact isQuartet_finite (coordinateRowFrame_isQuartet p)
    · exfalso
      apply coordinateQuartet_not_three_one p r hpr t _ hQ (by simp)
      intro c hc hne
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc
      rcases hc with rfl|rfl|rfl|h
      · exact ⟨x,rfl⟩
      · exact ⟨y,rfl⟩
      · exact ⟨z,rfl⟩
      · exact False.elim (hne h)
  · by_cases hpr : p=r
    · subst r
      exfalso
      apply coordinateQuartet_not_three_one p q hpq z _ hQ (by simp)
      intro c hc hne
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc
      rcases hc with rfl|rfl|h|rfl
      · exact ⟨x,rfl⟩
      · exact ⟨y,rfl⟩
      · exact False.elim (hne h)
      · exact ⟨t,rfl⟩
    · by_cases hqr : q=r
      · subst r
        obtain ⟨v,hv⟩ := coordinateQuartet_two_row_constructed p q hpq x y z t hxy hzt hQ
        exact ⟨Sum.inr v,hv⟩
      · exfalso
        apply coordinateQuartet_not_two_one_one p q r hqr x y z t hxy _ hQ (by simp) (by simp)
        intro c hc hcx hcy
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc
        rcases hc with h|h|h|h
        · exact False.elim (hcx h)
        · exact False.elim (hcy h)
        · exact Or.inl h
        · exact Or.inr h

end Atlas.Rudvalis
