import Atlas.Rudvalis.CoordinateQuartetInjection

namespace Atlas.Rudvalis

theorem coordinatePlaneQuartetFromParameters_mem (s : CoordinateRowPair) (f : s.val→Bit)
    (p : s.val) (x : E) :
    coordinateCross (p.val,x)∈coordinatePlaneQuartetFromParameters ⟨s,f⟩ ↔
      f p=dot (coordinateRowPairNormal s).val x := by
  constructor
  · rintro ⟨q,hq⟩
    have hpq : p=q := by
      apply Subtype.ext
      by_contra hn
      exact Set.disjoint_left.mp (coordinateRowFrame_disjoint hn)
        (show coordinateCross (p.val,x)∈coordinateRowFrame p.val from ⟨x,rfl⟩)
        (coordinatePlaneSlice_subset _ _ _ hq)
    subst q
    exact ((coordinatePlaneSlice_mem p.val _ (coordinateRowPairNormal_spec s p.val p.prop) (f p) x).mp hq).symm
  · intro h
    exact ⟨p,x,h.symm,rfl⟩

set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 2000000 in
theorem coordinateRowPair_value_card (s : CoordinateRowPair) (p : s.val) (b : Bit) :
    Nat.card {f : s.val→Bit // f p=b}=2 := by
  rw [Nat.card_eq_fintype_card]
  have cert : ∀s : Finset Point,s.card=2 → ∀p : s,∀b : Bit,
      Fintype.card {f : s→Bit // f p=b}=2 := by decide +kernel
  exact cert s.val s.prop p b

theorem coordinatePlaneQuartetFromParameters_fibre_card (s : CoordinateRowPair) (p : Point) (x : E) :
    Nat.card {f : s.val→Bit // coordinateCross (p,x)∈coordinatePlaneQuartetFromParameters ⟨s,f⟩}=
      if p∈s.val then 2 else 0 := by
  classical
  by_cases hp : p∈s.val
  · rw [ite_eq_left hp,Nat.card_congr (Equiv.subtypeEquivRight (fun f =>
      coordinatePlaneQuartetFromParameters_mem s f ⟨p,hp⟩ x))]
    exact coordinateRowPair_value_card s ⟨p,hp⟩ _
  · rw [ite_eq_right hp]
    have hn (f : s.val→Bit) : coordinateCross (p,x)∉coordinatePlaneQuartetFromParameters ⟨s,f⟩ := by
      intro h
      exact hp ((coordinatePlaneQuartetFromParameters_rows ⟨s,f⟩ p).mp ⟨_,h,⟨x,rfl⟩⟩)
    simp [hn,Nat.card_eq_fintype_card]

theorem coordinatePlaneQuartet_through_cross_card (p : Point) (x : E) :
    Nat.card {v : CoordinatePlaneQuartetParameters // coordinateCross (p,x)∈coordinatePlaneQuartetFromParameters v}=12 := by
  classical
  let e : {v : CoordinatePlaneQuartetParameters // coordinateCross (p,x)∈coordinatePlaneQuartetFromParameters v} ≃
      Σs : CoordinateRowPair,{f : s.val→Bit // coordinateCross (p,x)∈coordinatePlaneQuartetFromParameters ⟨s,f⟩} :=
    { toFun := fun v => ⟨v.val.1,⟨v.val.2,v.prop⟩⟩
      invFun := fun v => ⟨⟨v.1,v.2.val⟩,v.2.prop⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  simp_rw [coordinatePlaneQuartetFromParameters_fibre_card]
  have he : (∑s : CoordinateRowPair,if p∈s.val then (2 : ℕ) else 0)=
      ∑s ∈ Finset.univ.filter (fun s : CoordinateRowPair => p∈s.val),(2 : ℕ) := by
    rw [Finset.sum_filter]
  rw [he,Finset.sum_const]
  have hc : (Finset.univ.filter (fun s : CoordinateRowPair => p∈s.val)).card=6 := by
    have cert : ∀p : Point,(Finset.univ.filter (fun s : CoordinateRowPair => p∈s.val)).card=6 := by decide +kernel
    exact cert p
  rw [hc]; rfl

theorem coordinateCross_mem_row_iff (p q : Point) (x : E) :
    coordinateCross (p,x)∈coordinateRowFrame q ↔ q=p := by
  constructor
  · intro h
    by_contra hn
    exact Set.disjoint_left.mp (coordinateRowFrame_disjoint hn) h ⟨x,rfl⟩
  · rintro rfl
    exact ⟨x,rfl⟩

theorem coordinateQuartetConstruction_through_cross_card (p : Point) (x : E) :
    Nat.card {v : Point ⊕ CoordinatePlaneQuartetParameters // coordinateCross (p,x)∈coordinateQuartetConstruction v}=13 := by
  classical
  rw [Nat.card_congr Equiv.subtypeSum,Nat.card_sum]
  change Nat.card {q : Point // coordinateCross (p,x)∈coordinateRowFrame q}+
    Nat.card {v : CoordinatePlaneQuartetParameters // coordinateCross (p,x)∈coordinatePlaneQuartetFromParameters v}=13
  rw [coordinatePlaneQuartet_through_cross_card,Nat.card_congr (Equiv.subtypeEquivRight (fun q => coordinateCross_mem_row_iff p q x))]
  simp [Nat.card_eq_fintype_card]

/-- Exactly thirteen members of the constructed 91-quartet family contain each coordinate cross. -/
theorem coordinateConstructedQuartets_through_cross_card (p : Point) (x : E) :
    Nat.card {Q : Set.range coordinateQuartetConstruction // coordinateCross (p,x)∈Q.val}=13 := by
  let e := Equiv.ofInjective coordinateQuartetConstruction coordinateQuartetConstruction_injective
  let f : {v : Point ⊕ CoordinatePlaneQuartetParameters // coordinateCross (p,x)∈coordinateQuartetConstruction v} ≃
      {Q : Set.range coordinateQuartetConstruction // coordinateCross (p,x)∈Q.val} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  rw [←Nat.card_congr f]
  exact coordinateQuartetConstruction_through_cross_card p x

end Atlas.Rudvalis
