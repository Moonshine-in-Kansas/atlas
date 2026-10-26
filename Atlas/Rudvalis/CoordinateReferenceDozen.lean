import Atlas.Rudvalis.CoordinateQuartetClassification
import Atlas.Rudvalis.ReferenceConfigurations

namespace Atlas.Rudvalis

def referencePlaneNormal : Point := ⟨binaryLabel 1,by decide⟩

def ReferencePlaneParameters (v : CoordinatePlaneQuartetParameters) : Prop :=
  ∃h : rowLabel 0∈v.1.val,
    (∀q∈v.1.val,dot (binaryLabel 1) q.val=0) ∧ v.2 ⟨rowLabel 0,h⟩=0

instance (v : CoordinatePlaneQuartetParameters) : Decidable (ReferencePlaneParameters v) :=
  inferInstanceAs (Decidable (∃h : rowLabel 0∈v.1.val,
    (∀q∈v.1.val,dot (binaryLabel 1) q.val=0) ∧ v.2 ⟨rowLabel 0,h⟩=0))

theorem referencePlaneParameters_normal (v : CoordinatePlaneQuartetParameters)
    (hv : ReferencePlaneParameters v) : coordinateRowPairNormal v.1=referencePlaneNormal := by
  symm
  apply (coordinateRowPair_normal_exists v.1).choose_spec.2
  exact hv.choose_spec.1

theorem referencePlaneParameters_iff (v : CoordinatePlaneQuartetParameters) :
    referenceCouple⊆coordinatePlaneQuartetFromParameters v ↔ ReferencePlaneParameters v := by
  classical
  constructor
  · intro h
    have h0 := h (show localReferenceCross∈referenceCouple from by simp [referenceCouple])
    have h2 := h (show referenceSecondCross∈referenceCouple from by simp [referenceCouple])
    rw [localReferenceCross_eq] at h0
    rw [referenceSecondCross_eq] at h2
    have hp := (coordinatePlaneQuartetFromParameters_rows v (rowLabel 0)).mp ⟨_,h0,0,rfl⟩
    have he0 := (coordinatePlaneQuartetFromParameters_mem v.1 v.2 ⟨rowLabel 0,hp⟩ 0).mp h0
    have he2 := (coordinatePlaneQuartetFromParameters_mem v.1 v.2 ⟨rowLabel 0,hp⟩ (binaryLabel 2)).mp h2
    have hd0 : dot (coordinateRowPairNormal v.1).val 0=0 := by simp [dot]
    have he : coordinateRowPairNormal v.1=referencePlaneNormal := by
      have cert : ∀a : Point,dot a.val (rowLabel 0).val=0 →
          dot a.val (binaryLabel 2)=0 → a=referencePlaneNormal := by decide +kernel
      apply cert _ (coordinateRowPairNormal_spec v.1 _ hp)
      rw [←he2,he0,hd0]
    refine ⟨hp,?_,he0.trans hd0⟩
    intro q hq
    have hh := coordinateRowPairNormal_spec v.1 q hq
    rwa [he] at hh
  · intro hv
    obtain ⟨hp,ha,hf⟩ := hv
    have he := referencePlaneParameters_normal v ⟨hp,ha,hf⟩
    rintro c (rfl|rfl)
    · rw [localReferenceCross_eq]
      apply (coordinatePlaneQuartetFromParameters_mem v.1 v.2 ⟨rowLabel 0,hp⟩ 0).mpr
      rw [hf]; simp [dot]
    · rw [referenceSecondCross_eq]
      apply (coordinatePlaneQuartetFromParameters_mem v.1 v.2 ⟨rowLabel 0,hp⟩ (binaryLabel 2)).mpr
      rw [he,hf]
      decide +kernel

theorem referencePlaneParameters_fibre_card (s : CoordinateRowPair) :
    Nat.card {f : s.val→Bit // ReferencePlaneParameters ⟨s,f⟩}=
      if rowLabel 0∈s.val ∧ (∀q∈s.val,dot (binaryLabel 1) q.val=0) then 2 else 0 := by
  classical
  by_cases h : rowLabel 0∈s.val ∧ (∀q∈s.val,dot (binaryLabel 1) q.val=0)
  · rw [ite_eq_left h]
    have he (f : s.val→Bit) : ReferencePlaneParameters ⟨s,f⟩ ↔ f ⟨rowLabel 0,h.1⟩=0 := by
      constructor
      · rintro ⟨_,_,hf⟩; exact hf
      · intro hf; exact ⟨h.1,h.2,hf⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
    exact coordinateRowPair_value_card s ⟨rowLabel 0,h.1⟩ 0
  · rw [ite_eq_right h]
    have hn (f : s.val→Bit) : ¬ReferencePlaneParameters ⟨s,f⟩ := by
      rintro ⟨hp,ha,_⟩; exact h ⟨hp,ha⟩
    simp [hn,Nat.card_eq_fintype_card]

theorem referencePlaneParameters_card : Nat.card {v : CoordinatePlaneQuartetParameters // ReferencePlaneParameters v}=4 := by
  classical
  let e : {v : CoordinatePlaneQuartetParameters // ReferencePlaneParameters v} ≃
      Σs : CoordinateRowPair,{f : s.val→Bit // ReferencePlaneParameters ⟨s,f⟩} :=
    { toFun := fun v => ⟨v.val.1,⟨v.val.2,v.prop⟩⟩
      invFun := fun v => ⟨⟨v.1,v.2.val⟩,v.2.prop⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  simp_rw [referencePlaneParameters_fibre_card]
  have cert : (∑s : CoordinateRowPair,
      if rowLabel 0∈s.val ∧ (∀q∈s.val,dot (binaryLabel 1) q.val=0) then (2 : ℕ) else 0)=4 := by
    decide +kernel
  exact cert

theorem referenceCouple_subset_row_iff (p : Point) :
    referenceCouple⊆coordinateRowFrame p ↔ p=rowLabel 0 := by
  constructor
  · intro h
    have h0 := h (show localReferenceCross∈referenceCouple from by simp [referenceCouple])
    rw [localReferenceCross_eq] at h0
    exact (coordinateCross_mem_row_iff _ _ _).mp h0
  · rintro rfl c (rfl|rfl)
    · rw [localReferenceCross_eq]; exact ⟨0,rfl⟩
    · rw [referenceSecondCross_eq]; exact ⟨binaryLabel 2,rfl⟩

abbrev ReferenceCoordinateQuartets := {Q : CoordinateQuartets // referenceCouple⊆Q.val}

theorem referenceCoordinateQuartets_card : Nat.card ReferenceCoordinateQuartets=5 := by
  classical
  change Nat.card {Q : CoordinateQuartets // referenceCouple⊆Q.val}=5
  rw [coordinateQuartets_eq_constructed]
  let e := Equiv.ofInjective coordinateQuartetConstruction coordinateQuartetConstruction_injective
  let f : {v : Point ⊕ CoordinatePlaneQuartetParameters // referenceCouple⊆coordinateQuartetConstruction v} ≃
      {Q : Set.range coordinateQuartetConstruction // referenceCouple⊆Q.val} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  rw [←Nat.card_congr f,Nat.card_congr Equiv.subtypeSum,Nat.card_sum]
  change Nat.card {p : Point // referenceCouple⊆coordinateRowFrame p}+
    Nat.card {v : CoordinatePlaneQuartetParameters // referenceCouple⊆coordinatePlaneQuartetFromParameters v}=5
  rw [Nat.card_congr (Equiv.subtypeEquivRight referenceCouple_subset_row_iff),
    Nat.card_congr (Equiv.subtypeEquivRight referencePlaneParameters_iff),referencePlaneParameters_card]
  simp [Nat.card_eq_fintype_card]


/-- The union over coordinate quartets only; no global exhaustion is built into this definition. -/
def referenceCoordinateQuartetUnion : Set MinimalCross :=
  {x | ∃Q : Set MinimalCross,IsQuartet Q ∧ Q⊆coordinateFrame ∧ referenceCouple⊆Q ∧ x∈Q}

theorem referenceCoordinateQuartetUnion_eq :
    referenceCoordinateQuartetUnion=referenceCoordinateDozen := by
  classical
  apply Set.Subset.antisymm
  · rintro c ⟨Q,hQ,hF,hcouple,hc⟩
    obtain ⟨v,rfl⟩ := coordinateQuartet_classification Q hQ hF
    cases v with
    | inl p =>
      change referenceCouple⊆coordinateRowFrame p at hcouple
      have hp := referenceCouple_subset_row_iff p |>.mp hcouple
      subst p
      exact ⟨rowLabel 0,by change dot (binaryLabel 1) (rowLabel 0).val=0; decide +kernel,hc⟩
    | inr v =>
      have hv := (referencePlaneParameters_iff v).mp hcouple
      obtain ⟨p,hp⟩ := hc
      exact ⟨p.val,hv.choose_spec.1 p.val p.prop,coordinatePlaneSlice_subset _ _ _ hp⟩
  · rintro c ⟨p,hp,x,rfl⟩
    by_cases he : p=rowLabel 0
    · subst p
      exact ⟨coordinateRowFrame (rowLabel 0),coordinateRowFrame_isQuartet _,
        coordinateRowFrame_subset _,(referenceCouple_subset_row_iff _).mpr rfl,x,rfl⟩
    · let s : CoordinateRowPair := ⟨{rowLabel 0,p},by simp [Ne.symm he]⟩
      let f : s.val→Bit := fun q => if q.val=rowLabel 0 then 0 else dot (binaryLabel 1) x
      let v : CoordinatePlaneQuartetParameters := ⟨s,f⟩
      have h0 : rowLabel 0∈s.val := by simp [s]
      have hps : p∈s.val := by simp [s]
      have hv : ReferencePlaneParameters v := by
        refine ⟨h0,?_,?_⟩
        · intro q hq
          have hq2 : q=rowLabel 0 ∨ q=p := by simpa [v,s] using hq
          rcases hq2 with rfl|rfl
          · decide +kernel
          · exact hp
        · simp [v,f]
      refine ⟨coordinatePlaneQuartetFromParameters v,
        coordinatePlaneQuartetFromParameters_isQuartet _,
        coordinateQuartetConstruction_subset (Sum.inr v),
        (referencePlaneParameters_iff v).mpr hv,?_⟩
      apply (coordinatePlaneQuartetFromParameters_mem s f ⟨p,hps⟩ x).mpr
      rw [referencePlaneParameters_normal v hv]
      simp [f,he,referencePlaneNormal]

/-- The coordinate dozen really is contained in the intrinsically defined dozen. -/
theorem referenceCoordinateDozen_subset_intrinsicDozen :
    referenceCoordinateDozen⊆intrinsicDozen referenceCouple := by
  rw [←referenceCoordinateQuartetUnion_eq]
  rintro x ⟨Q,hQ,_,hc,hx⟩
  exact ⟨Q,hQ,hc,hx⟩

end Atlas.Rudvalis

