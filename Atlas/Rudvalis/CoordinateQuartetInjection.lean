import Atlas.Rudvalis.CoordinateQuartetParameters

namespace Atlas.Rudvalis

theorem dot_value_exists (a : Point) (δ : Bit) : ∃x : E,dot a.val x=δ := by
  obtain ⟨k,hk⟩ := point_has_one a
  refine ⟨δ • (basisPoint k).val,?_⟩
  rw [dot_smul_right,dot_comm a.val,dot_basisPoint,hk,mul_one]

theorem coordinatePlaneSlice_nonempty (p a : Point) (δ : Bit) : (coordinatePlaneSlice p a δ).Nonempty := by
  obtain ⟨x,hx⟩ := dot_value_exists a δ
  exact ⟨coordinateCross (p,x),x,hx,rfl⟩

theorem coordinatePlaneQuartetFromParameters_rows (v : CoordinatePlaneQuartetParameters) (p : Point) :
    (∃c,c∈coordinatePlaneQuartetFromParameters v ∧ c∈coordinateRowFrame p) ↔ p∈v.1.val := by
  constructor
  · rintro ⟨c,⟨q,hq⟩,hp⟩
    have he : p=q.val := by
      by_contra hn
      exact Set.disjoint_left.mp (coordinateRowFrame_disjoint hn) hp
        (coordinatePlaneSlice_subset _ _ _ hq)
    rw [he]
    exact q.prop
  · intro hp
    obtain ⟨c,hc⟩ := coordinatePlaneSlice_nonempty p (coordinateRowPairNormal v.1) (v.2 ⟨p,hp⟩)
    exact ⟨c,⟨⟨p,hp⟩,hc⟩,coordinatePlaneSlice_subset _ _ _ hc⟩

theorem coordinatePlaneQuartetFromParameters_injective : Function.Injective coordinatePlaneQuartetFromParameters := by
  rintro ⟨s,f⟩ ⟨t,g⟩ h
  have hst : s=t := by
    apply Subtype.ext
    apply Finset.ext
    intro p
    rw [←coordinatePlaneQuartetFromParameters_rows ⟨s,f⟩ p,
      ←coordinatePlaneQuartetFromParameters_rows ⟨t,g⟩ p,h]
  subst t
  have hfg : f=g := by
    funext p
    obtain ⟨x,hx⟩ := dot_value_exists (coordinateRowPairNormal s) (f p)
    have hc : coordinateCross (p.val,x)∈coordinatePlaneQuartetFromParameters ⟨s,f⟩ := ⟨p,x,hx,rfl⟩
    rw [h] at hc
    obtain ⟨q,hq⟩ := hc
    have hpq : p=q := by
      apply Subtype.ext
      by_contra hn
      exact Set.disjoint_left.mp (coordinateRowFrame_disjoint hn)
        (show coordinateCross (p.val,x)∈coordinateRowFrame p.val from ⟨x,rfl⟩)
        (coordinatePlaneSlice_subset _ _ _ hq)
    subst q
    have hy := (coordinatePlaneSlice_mem p.val (coordinateRowPairNormal s)
      (coordinateRowPairNormal_spec s p.val p.prop) (g p) x).mp hq
    exact hx.symm.trans hy
  subst g
  rfl

theorem coordinatePlaneQuartetFromParameters_range_card :
    Nat.card (Set.range coordinatePlaneQuartetFromParameters)=84 := by
  rw [←Nat.card_congr (Equiv.ofInjective coordinatePlaneQuartetFromParameters coordinatePlaneQuartetFromParameters_injective)]
  exact coordinatePlaneQuartetParameters_card

theorem coordinateRowFrame_injective : Function.Injective coordinateRowFrame := by
  intro p q h
  by_contra hn
  have hp : coordinateCross (p,0)∈coordinateRowFrame p := ⟨0,rfl⟩
  exact Set.disjoint_left.mp (coordinateRowFrame_disjoint hn) hp (h ▸ hp)

theorem coordinateRowFrame_ne_planeQuartet (p : Point) (v : CoordinatePlaneQuartetParameters) :
    coordinateRowFrame p≠coordinatePlaneQuartetFromParameters v := by
  intro h
  have hs : ∀q∈v.1.val,q=p := by
    intro q hq
    obtain ⟨c,hc,hcq⟩ := (coordinatePlaneQuartetFromParameters_rows v q).mpr hq
    rw [←h] at hc
    by_contra hn
    exact Set.disjoint_left.mp (coordinateRowFrame_disjoint hn) hcq hc
  have hsub : v.1.val⊆{p} := by intro q hq; simpa using hs q hq
  have hcard := Finset.card_le_card hsub
  rw [v.1.prop,Finset.card_singleton] at hcard
  omega

noncomputable def coordinateQuartetConstruction : Point ⊕ CoordinatePlaneQuartetParameters → Set MinimalCross :=
  Sum.elim coordinateRowFrame coordinatePlaneQuartetFromParameters

theorem coordinateQuartetConstruction_injective : Function.Injective coordinateQuartetConstruction := by
  intro a b h
  cases a with
  | inl p =>
    cases b with
    | inl q => exact congrArg Sum.inl (coordinateRowFrame_injective h)
    | inr v => exact False.elim (coordinateRowFrame_ne_planeQuartet p v h)
  | inr v =>
    cases b with
    | inl p => exact False.elim (coordinateRowFrame_ne_planeQuartet p v h.symm)
    | inr w => exact congrArg Sum.inr (coordinatePlaneQuartetFromParameters_injective h)

/-- Ninety-one distinct actual intrinsic coordinate quartets, before the exhaustion theorem. -/
theorem coordinateQuartetConstruction_card : Nat.card (Set.range coordinateQuartetConstruction)=91 := by
  rw [←Nat.card_congr (Equiv.ofInjective coordinateQuartetConstruction coordinateQuartetConstruction_injective),
    Nat.card_sum,coordinatePlaneQuartetParameters_card]
  have hp : Nat.card Point=7 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [hp]

theorem coordinateQuartetConstruction_isQuartet (v : Point ⊕ CoordinatePlaneQuartetParameters) :
    IsQuartet (coordinateQuartetConstruction v) := by
  cases v with
  | inl p => exact coordinateRowFrame_isQuartet p
  | inr v => exact coordinatePlaneQuartetFromParameters_isQuartet v

end Atlas.Rudvalis
