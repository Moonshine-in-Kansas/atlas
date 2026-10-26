import Atlas.Rudvalis.CoordinateRowCanonicalBase

namespace Atlas.Rudvalis

noncomputable def coordinatePlaneDozen (a : Point) : Set MinimalCross :=
  selectedCoordinateRows {q | dot a.val q.val=0}

theorem coordinatePlaneSlice_isCouple (p a : Point) (hap : dot a.val p.val=0) (δ : Bit) :
    IsCouple (coordinatePlaneSlice p a δ) :=
  ⟨coordinatePlaneSlice_card p a hap δ,
    (coordinateRowFrame_isQuartet p).2.1.mono (coordinatePlaneSlice_subset p a δ)⟩

theorem coordinateRow_couple_dozen_subset_of_reference
    (hD : intrinsicDozen referenceCouple=referenceCoordinateDozen)
    (p : Point) (c : Set MinimalCross) (hc : IsCouple c) (hp : c⊆coordinateRowFrame p) :
    intrinsicDozen c⊆coordinateFrame := by
  intro x hx
  rw [←coordinateRow_canonicalBase_eq_of_reference_dozen hD p]
  exact ⟨c,hc,hp,hx⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2048 in
theorem affine_plane_normal_unique (a b : Point) (δ ε : Bit)
    (h : ∀x : E,dot a.val x=δ → dot b.val x=ε) : a=b := by
  decide +kernel +revert

/-- Under the single reference exhaustion equality, each row-pair dozen is its three-row plane. -/
theorem coordinatePlaneSlice_dozen_eq_of_reference
    (hD : intrinsicDozen referenceCouple=referenceCoordinateDozen)
    (p a : Point) (hap : dot a.val p.val=0) (δ : Bit) :
    intrinsicDozen (coordinatePlaneSlice p a δ)=coordinatePlaneDozen a := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨Q,hQ,hc,hx⟩
    have hF : Q⊆coordinateFrame := by
      intro y hy
      exact coordinateRow_couple_dozen_subset_of_reference hD p _
        (coordinatePlaneSlice_isCouple p a hap δ) (coordinatePlaneSlice_subset p a δ) ⟨Q,hQ,hc,hy⟩
    obtain ⟨v,rfl⟩ := coordinateQuartet_classification Q hQ hF
    obtain ⟨z,hz⟩ := dot_value_exists a δ
    have hm := hc (show coordinateCross (p,z)∈coordinatePlaneSlice p a δ from ⟨z,hz,rfl⟩)
    cases v with
    | inl q =>
      have hpq := (coordinateCross_mem_row_iff p q z).mp hm
      subst q
      exact ⟨p,hap,hx⟩
    | inr v =>
      have hp := (coordinatePlaneQuartetFromParameters_rows v p).mp ⟨_,hm,z,rfl⟩
      have he : a=coordinateRowPairNormal v.1 := by
        apply affine_plane_normal_unique a _ δ (v.2 ⟨p,hp⟩)
        intro y hy
        exact ((coordinatePlaneQuartetFromParameters_mem v.1 v.2 ⟨p,hp⟩ y).mp
          (hc ⟨y,hy,rfl⟩)).symm
      obtain ⟨q,hq⟩ := hx
      refine ⟨q.val,?_,coordinatePlaneSlice_subset _ _ _ hq⟩
      rw [he]
      exact coordinateRowPairNormal_spec v.1 q.val q.prop
  · rintro x ⟨q,hq,z,rfl⟩
    by_cases hpq : p=q
    · subst q
      exact ⟨coordinateRowFrame p,coordinateRowFrame_isQuartet p,
        coordinatePlaneSlice_subset p a δ,z,rfl⟩
    · exact ⟨coordinatePlaneQuartet p q a δ (dot a.val z),
        coordinatePlaneQuartet_isQuartet p q a hpq hap hq δ (dot a.val z),
        Set.subset_union_left,Or.inr ⟨z,rfl,rfl⟩⟩

theorem coordinateRow_couple_eq_slice (p : Point) (c : Set MinimalCross)
    (hc : IsCouple c) (hp : c⊆coordinateRowFrame p) :
    ∃a : Point,∃δ : Bit,dot a.val p.val=0 ∧ c=coordinatePlaneSlice p a δ := by
  classical
  obtain ⟨u,v,huv,he⟩ := Set.ncard_eq_two.mp hc.1
  obtain ⟨x,rfl⟩ := hp (show u∈c from by rw [he];simp)
  obtain ⟨y,rfl⟩ := hp (show v∈c from by rw [he];simp)
  have hdiff := coordinateCross_difference_ne p x y huv
  let d : Point := ⟨y+x,hdiff.1⟩
  have hpd : p≠d := by intro h; exact hdiff.2 (congrArg Subtype.val h).symm
  let s : CoordinateRowPair := ⟨{p,d},by simp [hpd]⟩
  let a := coordinateRowPairNormal s
  have hap := coordinateRowPairNormal_spec s p (by simp [s])
  have had := coordinateRowPairNormal_spec s d (by simp [s])
  have hy : dot a.val y=dot a.val x := by
    change dot a.val (y+x)=0 at had
    rw [dot_add_right] at had
    have hi := congrArg (fun b : Bit => b+dot a.val x) had
    simpa only [add_assoc,CharTwo.add_self_eq_zero,add_zero,zero_add] using hi
  refine ⟨a,dot a.val x,hap,?_⟩
  apply Set.eq_of_subset_of_ncard_le ?_ ?_
  · rw [he]
    rintro z (rfl|rfl)
    · exact ⟨x,rfl,rfl⟩
    · exact ⟨y,hy,rfl⟩
  · change Nat.card (coordinatePlaneSlice p a (dot a.val x))≤c.ncard
    rw [coordinatePlaneSlice_card p a hap,hc.1]

def rowCoupleDozens (p : Point) : Set (Set MinimalCross) :=
  {D | ∃c : Set MinimalCross,IsCouple c ∧ c⊆coordinateRowFrame p ∧ intrinsicDozen c=D}

noncomputable def rowPlaneDozen (p : Point) (a : {a : Point // dot a.val p.val=0}) : Set MinimalCross :=
  coordinatePlaneDozen a.val

theorem rowCoupleDozens_eq_planes_of_reference
    (hD : intrinsicDozen referenceCouple=referenceCoordinateDozen) (p : Point) :
    rowCoupleDozens p=Set.range (rowPlaneDozen p) := by
  ext D
  constructor
  · rintro ⟨c,hc,hp,rfl⟩
    obtain ⟨a,δ,hap,rfl⟩ := coordinateRow_couple_eq_slice p c hc hp
    exact ⟨⟨a,hap⟩,(coordinatePlaneSlice_dozen_eq_of_reference hD p a hap δ).symm⟩
  · rintro ⟨a,rfl⟩
    exact ⟨coordinatePlaneSlice p a.val 0,coordinatePlaneSlice_isCouple p a.val a.prop 0,
      coordinatePlaneSlice_subset p a.val 0,coordinatePlaneSlice_dozen_eq_of_reference hD p a.val a.prop 0⟩


theorem coordinatePlaneDozen_injective : Function.Injective coordinatePlaneDozen := by
  intro a b h
  apply affine_plane_normal_unique a b 0 0
  intro x hx
  by_cases hzero : x=0
  · rw [hzero]; simp [dot]
  · let q : Point := ⟨x,hzero⟩
    have hm : coordinateCross (q,0)∈coordinatePlaneDozen a := ⟨q,hx,0,rfl⟩
    rw [h] at hm
    exact (coordinateCross_mem_selectedRows_iff _ _).mp hm

theorem rowPlaneDozen_injective (p : Point) : Function.Injective (rowPlaneDozen p) := by
  intro a b h
  exact Subtype.ext (coordinatePlaneDozen_injective h)

theorem rowPlaneNormals_card (p : Point) : Nat.card {a : Point // dot a.val p.val=0}=3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel +revert

theorem rowCoupleDozens_card_of_reference
    (hD : intrinsicDozen referenceCouple=referenceCoordinateDozen) (p : Point) :
    Nat.card (rowCoupleDozens p)=3 := by
  rw [rowCoupleDozens_eq_planes_of_reference hD p,
    ←Nat.card_congr (Equiv.ofInjective (rowPlaneDozen p) (rowPlaneDozen_injective p)),rowPlaneNormals_card]

theorem coordinatePlaneDozen_card (a : Point) : Nat.card (coordinatePlaneDozen a)=12 := by
  rw [coordinatePlaneDozen,selectedCoordinateRows_card]
  have hc : Nat.card {q : Point // dot a.val q.val=0}=3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel +revert
  change Nat.card {q : Point // dot a.val q.val=0}*4=12
  rw [hc]

set_option synthInstance.maxSize 2048 in
theorem rowPlaneDozen_intersection (p : Point) (a b : {a : Point // dot a.val p.val=0})
    (hab : a≠b) : rowPlaneDozen p a∩rowPlaneDozen p b=coordinateRowFrame p := by
  have hn : a.val≠b.val := fun h=>hab (Subtype.ext h)
  have cert : ∀p a b q : Point,a≠b → dot a.val p.val=0 → dot b.val p.val=0 →
      (dot a.val q.val=0 ∧ dot b.val q.val=0 ↔ q=p) := by decide +kernel
  ext c
  constructor
  · rintro ⟨⟨q,hq,hc⟩,⟨r,hr,hd⟩⟩
    have he : q=r := by
      obtain ⟨x,hx⟩ := hc
      obtain ⟨y,hy⟩ := hd
      exact coordinateCross_row_of_eq (hx.trans hy.symm)
    subst r
    have hqp := (cert p a.val b.val q hn a.prop b.prop).mp ⟨hq,hr⟩
    simpa only [hqp] using hc
  · intro hc
    exact ⟨⟨p,a.prop,hc⟩,⟨p,b.prop,hc⟩⟩

theorem rowPlaneDozens_union (p : Point) :
    {c | ∃a : {a : Point // dot a.val p.val=0},c∈rowPlaneDozen p a}=coordinateFrame := by
  ext c
  constructor
  · rintro ⟨a,hc⟩
    exact selectedCoordinateRows_subset _ hc
  · intro hc
    obtain ⟨⟨q,x⟩,rfl⟩ := coordinateFrame_rep c hc
    have cert : ∀p q : Point,∃a : Point,dot a.val p.val=0 ∧ dot a.val q.val=0 := by decide +kernel
    obtain ⟨a,hap,haq⟩ := cert p q
    exact ⟨⟨a,hap⟩,q,haq,x,rfl⟩

end Atlas.Rudvalis

