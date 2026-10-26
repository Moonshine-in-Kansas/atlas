import Atlas.Rudvalis.CoordinateFourRowObstruction
import Atlas.Rudvalis.CoordinateQuartetRepeatedRow

namespace Atlas.Rudvalis

private theorem equal_row_constructed (i j k l : Coordinate) (hr : i.1=j.1)
    (hij : coordinateCross i≠coordinateCross j) (hkl : coordinateCross k≠coordinateCross l)
    (hQ : IsQuartet {coordinateCross i,coordinateCross j,coordinateCross k,coordinateCross l}) :
    {coordinateCross i,coordinateCross j,coordinateCross k,coordinateCross l}∈Set.range coordinateQuartetConstruction := by
  rcases i with ⟨p,x⟩
  rcases j with ⟨q,y⟩
  rcases k with ⟨r,z⟩
  rcases l with ⟨s,t⟩
  change p=q at hr
  subst q
  exact coordinateQuartet_repeated_row p r s x y z t hij hkl hQ

private theorem four_set_permute (a b c d : MinimalCross) :
    ({a,c,b,d} : Set MinimalCross)={a,b,c,d} ∧
    ({a,d,b,c} : Set MinimalCross)={a,b,c,d} ∧
    ({b,c,a,d} : Set MinimalCross)={a,b,c,d} ∧
    ({b,d,a,c} : Set MinimalCross)={a,b,c,d} ∧
    ({c,d,a,b} : Set MinimalCross)={a,b,c,d} := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto

theorem coordinateQuartet_constructed_or_distinct_rows (i j k l : Coordinate)
    (hij : coordinateCross i≠coordinateCross j) (hik : coordinateCross i≠coordinateCross k)
    (hil : coordinateCross i≠coordinateCross l) (hjk : coordinateCross j≠coordinateCross k)
    (hjl : coordinateCross j≠coordinateCross l) (hkl : coordinateCross k≠coordinateCross l)
    (hQ : IsQuartet {coordinateCross i,coordinateCross j,coordinateCross k,coordinateCross l}) :
    {coordinateCross i,coordinateCross j,coordinateCross k,coordinateCross l}∈Set.range coordinateQuartetConstruction ∨
      Function.Injective (![i.1,j.1,k.1,l.1] : Fin 4→Point) := by
  have hs := four_set_permute (coordinateCross i) (coordinateCross j) (coordinateCross k) (coordinateCross l)
  by_cases h01 : i.1=j.1
  · exact Or.inl (equal_row_constructed i j k l h01 hij hkl hQ)
  by_cases h02 : i.1=k.1
  · left
    have h := equal_row_constructed i k j l h02 hik hjl (by rwa [hs.1])
    rwa [hs.1] at h
  by_cases h03 : i.1=l.1
  · left
    have h := equal_row_constructed i l j k h03 hil hjk (by rwa [hs.2.1])
    rwa [hs.2.1] at h
  by_cases h12 : j.1=k.1
  · left
    have h := equal_row_constructed j k i l h12 hjk hil (by rwa [hs.2.2.1])
    rwa [hs.2.2.1] at h
  by_cases h13 : j.1=l.1
  · left
    have h := equal_row_constructed j l i k h13 hjl hik (by rwa [hs.2.2.2.1])
    rwa [hs.2.2.2.1] at h
  by_cases h23 : k.1=l.1
  · left
    have h := equal_row_constructed k l i j h23 hkl hij (by rwa [hs.2.2.2.2])
    rwa [hs.2.2.2.2] at h
  right
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

theorem coordinateFourSet_range (i j k l : Coordinate) :
    ({coordinateCross i,coordinateCross j,coordinateCross k,coordinateCross l} : Set MinimalCross)=
      Set.range (fun n : Fin 4 => coordinateCross (![i.1,j.1,k.1,l.1] n,![i.2,j.2,k.2,l.2] n)) := by
  ext c
  constructor
  · intro h
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  · rintro ⟨n,rfl⟩
    fin_cases n <;> simp

/-- Pure multiplicity assembly, with the four-distinct-row obstruction explicit. -/
theorem coordinateQuartet_classification_of_four_row_obstruction
    (hfour : ∀(Q : Set MinimalCross),IsQuartet Q → ∀(p : Fin 4→Point)(x : Fin 4→E),
      Function.Injective p → Q=Set.range (fun i => coordinateCross (p i,x i)) → False)
    (Q : Set MinimalCross) (hQ : IsQuartet Q) (hF : Q⊆coordinateFrame) :
    Q∈Set.range coordinateQuartetConstruction := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hQeq⟩ := Set.ncard_eq_four.mp hQ.1
  have ha : a∈coordinateFrame := hF (by rw [hQeq]; simp)
  have hb : b∈coordinateFrame := hF (by rw [hQeq]; simp)
  have hc : c∈coordinateFrame := hF (by rw [hQeq]; simp)
  have hd : d∈coordinateFrame := hF (by rw [hQeq]; simp)
  obtain ⟨i,rfl⟩ := coordinateFrame_rep a ha
  obtain ⟨j,rfl⟩ := coordinateFrame_rep b hb
  obtain ⟨k,rfl⟩ := coordinateFrame_rep c hc
  obtain ⟨l,rfl⟩ := coordinateFrame_rep d hd
  subst Q
  rcases coordinateQuartet_constructed_or_distinct_rows i j k l hab hac had hbc hbd hcd hQ with h|h
  · exact h
  · exact False.elim (hfour _ hQ _ _ h (coordinateFourSet_range i j k l))


def CoordinateQuartets : Set (Set MinimalCross) := {Q | IsQuartet Q ∧ Q⊆coordinateFrame}

theorem coordinateQuartetConstruction_subset (v : Point ⊕ CoordinatePlaneQuartetParameters) :
    coordinateQuartetConstruction v⊆coordinateFrame := by
  cases v with
  | inl p => exact coordinateRowFrame_subset p
  | inr v =>
    rintro c ⟨p,hp⟩
    exact coordinateRowFrame_subset p.val (coordinatePlaneSlice_subset _ _ _ hp)

/-- Exhaustive intrinsic classification of the quartets contained in the coordinate frame. -/
theorem coordinateQuartet_classification (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (hF : Q⊆coordinateFrame) : Q∈Set.range coordinateQuartetConstruction :=
  coordinateQuartet_classification_of_four_row_obstruction coordinateQuartet_not_four_distinct_rows Q hQ hF

theorem coordinateQuartets_eq_constructed : CoordinateQuartets=Set.range coordinateQuartetConstruction := by
  ext Q
  constructor
  · rintro ⟨hQ,hF⟩
    exact coordinateQuartet_classification Q hQ hF
  · rintro ⟨v,rfl⟩
    exact ⟨coordinateQuartetConstruction_isQuartet v,coordinateQuartetConstruction_subset v⟩

/-- There are exactly91 intrinsic quartets in the original coordinate frame. -/
theorem coordinateQuartets_card : Nat.card CoordinateQuartets=91 := by
  rw [coordinateQuartets_eq_constructed]
  exact coordinateQuartetConstruction_card

/-- Every coordinate cross lies in exactly13 intrinsic coordinate quartets. -/
theorem coordinateQuartets_through_cross_card (c : coordinateFrame) :
    Nat.card {Q : CoordinateQuartets // c.val∈Q.val}=13 := by
  obtain ⟨i,hi⟩ := coordinateFrame_rep c.val c.prop
  rw [←hi,coordinateQuartets_eq_constructed]
  exact coordinateConstructedQuartets_through_cross_card i.1 i.2

end Atlas.Rudvalis
