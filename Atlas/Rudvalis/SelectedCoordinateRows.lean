import Atlas.Rudvalis.CoordinateCommonPerpendicular

namespace Atlas.Rudvalis

noncomputable def selectedCoordinateRows (s : Set Point) : Set MinimalCross :=
  {c | ∃p∈s,c∈coordinateRowFrame p}

theorem selectedCoordinateRows_subset (s : Set Point) : selectedCoordinateRows s⊆coordinateFrame := by
  rintro c ⟨p,hp,hc⟩
  exact coordinateRowFrame_subset p hc

theorem selectedCoordinateRowFrames_disjoint (p q : Point) (hpq : p≠q) :
    Disjoint (coordinateRowFrame p) (coordinateRowFrame q) := by
  apply Set.disjoint_left.mpr
  rintro c ⟨x,hx⟩ ⟨y,hy⟩
  exact hpq (coordinateCross_row_of_eq (hx.trans hy.symm))

noncomputable def selectedCoordinateRowsEquiv (s : Set Point) :
    (Σ p : s,coordinateRowFrame p.val) ≃ selectedCoordinateRows s :=
  Equiv.ofBijective (fun a => ⟨a.2.val,a.1.val,a.1.prop,a.2.prop⟩) (by
    constructor
    · intro a b h
      obtain ⟨⟨p,hp⟩,c⟩ := a
      obtain ⟨⟨q,hq⟩,d⟩ := b
      have hc : c.val=d.val := congrArg Subtype.val h
      have hpq : p=q := by
        obtain ⟨x,hx⟩ := c.prop
        obtain ⟨y,hy⟩ := d.prop
        exact coordinateCross_row_of_eq (hx.trans (hc.trans hy.symm))
      subst q
      have hcd : c=d := Subtype.ext hc
      subst d
      rfl
    · rintro ⟨c,p,hp,hc⟩
      exact ⟨⟨⟨p,hp⟩,⟨c,hc⟩⟩,rfl⟩)

theorem selectedCoordinateRows_card (s : Set Point) :
    Nat.card (selectedCoordinateRows s)=Nat.card s*4 := by
  classical
  let : Fintype s := Fintype.ofFinite _
  rw [←Nat.card_congr (selectedCoordinateRowsEquiv s),Nat.card_sigma]
  simp_rw [coordinateRowFrame_card]
  simp [Nat.card_eq_fintype_card]

def referenceDozenRows : Set Point := {p | dot (binaryLabel 1) p.val=0}

noncomputable def referenceCoordinateDozen : Set MinimalCross := selectedCoordinateRows referenceDozenRows

theorem referenceDozenRows_card : Nat.card referenceDozenRows=3 := by
  change Nat.card {p : Point // dot (binaryLabel 1) p.val=0}=3
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem referenceCoordinateDozen_card : Nat.card referenceCoordinateDozen=12 := by
  rw [referenceCoordinateDozen,selectedCoordinateRows_card,referenceDozenRows_card]

theorem referenceCoordinateDozen_subset : referenceCoordinateDozen⊆coordinateFrame :=
  selectedCoordinateRows_subset _

theorem referenceCross_mem_dozen : localReferenceCross∈referenceCoordinateDozen := by
  rw [localReferenceCross_eq]
  exact ⟨rowLabel 0,by change dot (binaryLabel 1) (rowLabel 0).val=0; decide +kernel,0,rfl⟩

theorem referenceSecondCross_mem_dozen : referenceSecondCross∈referenceCoordinateDozen := by
  rw [referenceSecondCross_eq]
  exact ⟨rowLabel 0,by change dot (binaryLabel 1) (rowLabel 0).val=0; decide +kernel,binaryLabel 2,rfl⟩

theorem referenceCoordinateDozen_outside_card : Nat.card ↥(coordinateFrame\referenceCoordinateDozen)=16 := by
  change (coordinateFrame\referenceCoordinateDozen).ncard=16
  rw [Set.ncard_sdiff referenceCoordinateDozen_subset]
  change Nat.card coordinateFrame-Nat.card referenceCoordinateDozen=16
  rw [coordinateFrame_card,referenceCoordinateDozen_card]

theorem referenceCoordinateDozen_complement_pair_card :
    Nat.card ↥((referenceCoordinateDozen\{localReferenceCross})\{referenceSecondCross})=10 := by
  change ((referenceCoordinateDozen\{localReferenceCross})\{referenceSecondCross}).ncard=10
  rw [Set.ncard_sdiff_singleton_of_mem
      (show referenceSecondCross∈referenceCoordinateDozen\{localReferenceCross} from
        ⟨referenceSecondCross_mem_dozen,Ne.symm reference_crosses_ne⟩),
    Set.ncard_sdiff_singleton_of_mem referenceCross_mem_dozen]
  change Nat.card referenceCoordinateDozen-1-1=10
  rw [referenceCoordinateDozen_card]

theorem coordinateCross_mem_selectedRows_iff (s : Set Point) (i : Coordinate) :
    coordinateCross i∈selectedCoordinateRows s ↔ i.1∈s := by
  constructor
  · rintro ⟨p,hp,z,hz⟩
    have he := coordinateCross_row_of_eq hz
    exact he ▸ hp
  · intro h
    exact ⟨i.1,h,i.2,rfl⟩

end Atlas.Rudvalis

