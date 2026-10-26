import Atlas.Rudvalis.CoordinateTripleFrame
import Atlas.Rudvalis.CoordinateReferenceDozen

namespace Atlas.Rudvalis

/-- Three distinct coordinate members force an entire intrinsic quartet into the coordinate frame. -/
theorem quartet_containing_three_coordinate (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (a b c : MinimalCross) (ha : a∈Q) (hb : b∈Q) (hc : c∈Q)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (haF : a∈coordinateFrame) (hbF : b∈coordinateFrame) (hcF : c∈coordinateFrame) :
    Q⊆coordinateFrame := by
  intro w hw
  by_contra hwF
  have haw : a≠w := fun h=>hwF (h ▸ haF)
  have hbw : b≠w := fun h=>hwF (h ▸ hbF)
  have hcw : c≠w := fun h=>hwF (h ▸ hcF)
  have hs : ({a,b,c,w} : Set MinimalCross)⊆Q := by
    rintro z (rfl|rfl|rfl|rfl) <;> assumption
  have hn : ({a,b,c,w} : Set MinimalCross).ncard=4 :=
    Set.ncard_eq_four.mpr ⟨a,b,c,w,hab,hac,haw,hbc,hbw,hcw,rfl⟩
  have he : ({a,b,c,w} : Set MinimalCross)=Q :=
    Set.eq_of_subset_of_ncard_le hs (by rw [hQ.1,hn])
  apply hwF (quartet_three_in_coordinateFrame Q hQ w hw ?_)
  intro z hz hzw
  rw [←he] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact haF
  · exact hbF
  · exact hcF
  · exact (hzw rfl).elim

theorem reference_quartet_coordinate_member_in_dozen (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (hc : referenceCouple⊆Q) (z : MinimalCross) (hz : z∈Q) (hzF : z∈coordinateFrame) :
    z∈referenceCoordinateDozen := by
  by_cases hx : z=localReferenceCross
  · exact hx ▸ referenceCross_mem_dozen
  by_cases hy : z=referenceSecondCross
  · exact hy ▸ referenceSecondCross_mem_dozen
  have hF := quartet_containing_three_coordinate Q hQ localReferenceCross referenceSecondCross z
    (hc (Or.inl rfl)) (hc (Or.inr rfl)) hz reference_crosses_ne (Ne.symm hx) (Ne.symm hy)
    (coordinateCross_mem _) (coordinateCross_mem _) hzF
  rw [←referenceCoordinateQuartetUnion_eq]
  exact ⟨Q,hQ,hF,hc,hz⟩

theorem reference_no_quartet_through_outside_coordinate (z : MinimalCross)
    (hzF : z∈coordinateFrame) (hzD : z∉referenceCoordinateDozen) :
    ¬∃Q : Set MinimalCross,IsQuartet Q ∧ referenceCouple⊆Q ∧ z∈Q := by
  rintro ⟨Q,hQ,hc,hz⟩
  exact hzD (reference_quartet_coordinate_member_in_dozen Q hQ hc z hz hzF)

theorem coordinateQuartet_rows_at_most_two (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (hF : Q⊆coordinateFrame) :
    ∃s : Finset Point,s.card≤2 ∧ ∀i : Coordinate,coordinateCross i∈Q → i.1∈s := by
  classical
  obtain ⟨v,rfl⟩ := coordinateQuartet_classification Q hQ hF
  cases v with
  | inl p =>
    refine ⟨{p},by simp,?_⟩
    intro i hi
    obtain ⟨x,hx⟩ := hi
    have he := coordinateCross_row_of_eq hx
    simpa only [Finset.mem_singleton] using he.symm
  | inr v =>
    refine ⟨v.1.val,by rw [v.1.prop],?_⟩
    intro i hi
    exact (coordinatePlaneQuartetFromParameters_rows v i.1).mp
      ⟨coordinateCross i,hi,i.2,rfl⟩

theorem no_quartet_through_three_coordinate_rows (i j k : Coordinate)
    (hij : i.1≠j.1) (hik : i.1≠k.1) (hjk : j.1≠k.1) :
    ¬∃Q : Set MinimalCross,IsQuartet Q ∧ coordinateCross i∈Q ∧
      coordinateCross j∈Q ∧ coordinateCross k∈Q := by
  classical
  rintro ⟨Q,hQ,hi,hj,hk⟩
  have hF := quartet_containing_three_coordinate Q hQ _ _ _ hi hj hk
    (fun h=>hij (coordinateCross_row_of_eq h))
    (fun h=>hik (coordinateCross_row_of_eq h))
    (fun h=>hjk (coordinateCross_row_of_eq h))
    (coordinateCross_mem i) (coordinateCross_mem j) (coordinateCross_mem k)
  obtain ⟨s,hs,hm⟩ := coordinateQuartet_rows_at_most_two Q hQ hF
  have hsub : ({i.1,j.1,k.1} : Finset Point)⊆s := by
    intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl
    · exact hm i hi
    · exact hm j hj
    · exact hm k hk
  have hc := Finset.card_le_card hsub
  have hn : ({i.1,j.1,k.1} : Finset Point).card=3 := by simp [hij,hik,hjk]
  omega

end Atlas.Rudvalis
