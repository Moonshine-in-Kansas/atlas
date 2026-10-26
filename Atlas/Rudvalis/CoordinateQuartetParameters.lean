import Atlas.Rudvalis.CoordinatePlaneQuartets

namespace Atlas.Rudvalis

abbrev CoordinateRowPair := {s : Finset Point // s.card=2}

theorem coordinateRowPair_card : Nat.card CoordinateRowPair=21 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 2000000 in
theorem coordinateRowPair_normal_exists (s : CoordinateRowPair) :
    ∃!a : Point,∀p∈s.val,dot a.val p.val=0 := by
  rcases s with ⟨s,hs⟩
  change ∃!a : Point,∀p∈s,dot a.val p.val=0
  simp only [ExistsUnique]
  decide +kernel +revert

noncomputable def coordinateRowPairNormal (s : CoordinateRowPair) : Point :=
  (coordinateRowPair_normal_exists s).choose

theorem coordinateRowPairNormal_spec (s : CoordinateRowPair) (p : Point) (hp : p∈s.val) :
    dot (coordinateRowPairNormal s).val p.val=0 :=
  (coordinateRowPair_normal_exists s).choose_spec.1 p hp

abbrev CoordinatePlaneQuartetParameters := Σs : CoordinateRowPair,s.val→Bit

theorem coordinatePlaneQuartetParameters_card : Nat.card CoordinatePlaneQuartetParameters=84 := by
  classical
  rw [Nat.card_sigma]
  have hc (s : CoordinateRowPair) : Nat.card (s.val→Bit)=4 := by
    simp [Nat.card_eq_fintype_card,s.prop,Bit,ZMod.card]
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,coordinateRowPair_card]

noncomputable def coordinatePlaneQuartetFromParameters (v : CoordinatePlaneQuartetParameters) : Set MinimalCross :=
  {c | ∃p : v.1.val,c∈coordinatePlaneSlice p.val (coordinateRowPairNormal v.1) (v.2 p)}

theorem coordinatePlaneQuartetFromParameters_member (v : CoordinatePlaneQuartetParameters) (p : v.1.val)
    (c : MinimalCross) (hc : c∈coordinatePlaneSlice p.val (coordinateRowPairNormal v.1) (v.2 p)) :
    c∈coordinatePlaneQuartetFromParameters v := ⟨p,hc⟩

theorem coordinatePlaneQuartetFromParameters_eq (v : CoordinatePlaneQuartetParameters)
    (p q : Point) (hpq : p≠q) (hs : v.1.val={p,q}) :
    coordinatePlaneQuartetFromParameters v=
      coordinatePlaneQuartet p q (coordinateRowPairNormal v.1)
        (v.2 ⟨p,by rw [hs]; simp⟩) (v.2 ⟨q,by rw [hs]; simp⟩) := by
  classical
  ext c
  constructor
  · rintro ⟨⟨r,hr⟩,hc⟩
    rw [hs,Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl|rfl
    · exact Or.inl hc
    · exact Or.inr hc
  · rintro (hc|hc)
    · exact ⟨⟨p,by rw [hs]; simp⟩,hc⟩
    · exact ⟨⟨q,by rw [hs]; simp⟩,hc⟩

theorem coordinatePlaneQuartetFromParameters_isQuartet (v : CoordinatePlaneQuartetParameters) :
    IsQuartet (coordinatePlaneQuartetFromParameters v) := by
  obtain ⟨p,q,hpq,hs⟩ := Finset.card_eq_two.mp v.1.prop
  rw [coordinatePlaneQuartetFromParameters_eq v p q hpq hs]
  apply coordinatePlaneQuartet_isQuartet p q _ hpq
  · exact coordinateRowPairNormal_spec v.1 p (by rw [hs]; simp)
  · exact coordinateRowPairNormal_spec v.1 q (by rw [hs]; simp)

end Atlas.Rudvalis
