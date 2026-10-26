import Atlas.Rudvalis.CoordinateCrossOrthogonality

namespace Atlas.Rudvalis

theorem coordinateCross_eq_iff (i j : Coordinate) :
    coordinateCross i=coordinateCross j ↔ i=j ∨ codeI.val.right i=j := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have ho : CrossOrthogonal (coordinateCross i) (coordinateCross j) := by
      apply (crossOrthogonal_mk _ _).mpr
      change HermitianOrthogonal (coordinateMinimum i) (coordinateMinimum j)
      rw [coordinate_hermitianOrthogonal]
      simp [coordinateMinimum,Ne.symm hn.1,Ne.symm hn.2]
    rw [h] at ho
    exact crossOrthogonal_irrefl _ ho
  · rintro (rfl|he)
    · rfl
    · rw [←he,coordinateCross_I]

noncomputable def coordinateRowFrame (p : Point) : Set MinimalCross :=
  Set.range (fun x : E => coordinateCross (p,x))

theorem coordinateRowFrame_subset (p : Point) : coordinateRowFrame p⊆coordinateFrame := by
  rintro c ⟨x,rfl⟩
  exact coordinateCross_mem _

noncomputable def coordinateRowParamEquiv (p : Point) (k : Fin 3) (hp : p.val k=1) :
    {x : E // x k=0} ≃ coordinateRowFrame p :=
  Equiv.ofBijective (fun x => ⟨coordinateCross (p,x.val),⟨x.val,rfl⟩⟩) (by
    constructor
    · intro x y h
      have he := (coordinateCross_eq_iff _ _).mp (congrArg Subtype.val h)
      apply Subtype.ext
      rcases he with he|he
      · exact congrArg Prod.snd he
      · rw [codeI_coordinate] at he
        have hk := congrArg (fun z : Coordinate => z.2 k) he
        change x.val k+p.val k=y.val k at hk
        rw [x.prop,y.prop,hp] at hk
        norm_num at hk
    · rintro ⟨c,x,rfl⟩
      by_cases hx : x k=0
      · exact ⟨⟨x,hx⟩,rfl⟩
      · have hb : ∀a : Bit,a≠0 → a+1=0 := by decide +kernel
        refine ⟨⟨x+p.val,?_⟩,?_⟩
        · change x k+p.val k=0
          rw [hp]
          exact hb _ hx
        · apply Subtype.ext
          simpa only [codeI_coordinate] using coordinateCross_I (p,x))

theorem coordinateRowFrame_card (p : Point) : Nat.card (coordinateRowFrame p)=4 := by
  obtain ⟨k,hk⟩ := point_has_one p
  rw [←Nat.card_congr (coordinateRowParamEquiv p k hk),Nat.card_eq_fintype_card]
  have hc : ∀j : Fin 3,Fintype.card {x : E // x j=0}=4 := by decide +kernel
  exact hc k

theorem coordinateRowFrame_orthogonal_card (p : Point) (x : coordinateRowFrame p) :
    Nat.card {y : coordinateRowFrame p // CrossOrthogonal x.val y.val}=3 := by
  classical
  let : Fintype (coordinateRowFrame p) := Fintype.ofFinite _
  let e : {y : coordinateRowFrame p // CrossOrthogonal x.val y.val} ≃
      {y : coordinateRowFrame p // ¬y=x} :=
    Equiv.subtypeEquivRight (fun y => by
      rw [coordinateFrame_orthogonal_iff _ _ (coordinateRowFrame_subset p x.prop)
        (coordinateRowFrame_subset p y.prop)]
      exact not_congr (Subtype.ext_iff.symm.trans eq_comm))
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  have hc : Fintype.card (coordinateRowFrame p)=4 := by
    simpa [Nat.card_eq_fintype_card] using coordinateRowFrame_card p
  simp [hc]

theorem coordinateFrame_outside_row_card (p : Point) :
    Nat.card {y : coordinateFrame // y.val∉coordinateRowFrame p}=24 := by
  classical
  let : Fintype coordinateFrame := Fintype.ofFinite _
  let e : {y : coordinateFrame // y.val∈coordinateRowFrame p} ≃ coordinateRowFrame p :=
    { toFun := fun y => ⟨y.val.val,y.prop⟩
      invFun := fun y => ⟨⟨y.val,coordinateRowFrame_subset p y.prop⟩,y.prop⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  have hr : Fintype.card {y : coordinateFrame // y.val∈coordinateRowFrame p}=4 := by
    rw [←Nat.card_eq_fintype_card,Nat.card_congr e,coordinateRowFrame_card]
  have hc : Fintype.card coordinateFrame=28 := by
    simpa [Nat.card_eq_fintype_card] using coordinateFrame_card
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,hr,hc]

theorem coordinateFrame_outside_row_orthogonal (p : Point) (x : coordinateRowFrame p)
    (y : coordinateFrame) (hy : y.val∉coordinateRowFrame p) :
    CrossOrthogonal x.val y.val := by
  apply (coordinateFrame_orthogonal_iff _ _ (coordinateRowFrame_subset p x.prop) y.prop).mpr
  intro he
  exact hy (he ▸ x.prop)

end Atlas.Rudvalis
