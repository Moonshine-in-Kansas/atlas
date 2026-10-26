import Atlas.Rudvalis.CoordinateRowQuartets

namespace Atlas.Rudvalis

def coordinatePlaneSlice (p a : Point) (δ : Bit) : Set MinimalCross :=
  {c | ∃x : E,dot a.val x=δ ∧ coordinateCross (p,x)=c}

theorem coordinatePlaneSlice_subset (p a : Point) (δ : Bit) :
    coordinatePlaneSlice p a δ⊆coordinateRowFrame p := by
  rintro c ⟨x,_,rfl⟩
  exact ⟨x,rfl⟩

theorem coordinatePlaneSlice_mem (p a : Point) (hap : dot a.val p.val=0) (δ : Bit) (x : E) :
    coordinateCross (p,x)∈coordinatePlaneSlice p a δ ↔ dot a.val x=δ := by
  constructor
  · rintro ⟨y,hy,he⟩
    rcases (coordinateCross_eq_iff _ _).mp he with he|he
    · have h := congrArg Prod.snd he
      change y=x at h
      rwa [h] at hy
    · rw [codeI_coordinate] at he
      have h := congrArg Prod.snd he
      change y+p.val=x at h
      rw [←h,dot_add_right,hap,add_zero]
      exact hy
  · intro h
    exact ⟨x,h,rfl⟩

theorem coordinateRowFrame_disjoint {p q : Point} (hpq : p≠q) :
    Disjoint (coordinateRowFrame p) (coordinateRowFrame q) := by
  apply Set.disjoint_left.mpr
  rintro c ⟨x,rfl⟩ ⟨y,hy⟩
  rcases (coordinateCross_eq_iff _ _).mp hy with h|h
  · exact hpq (congrArg Prod.fst h).symm
  · rw [codeI_coordinate] at h
    exact hpq (congrArg Prod.fst h).symm

noncomputable def coordinateRowSliceEquiv (p a : Point) (δ : Bit) :
    {c : coordinateRowFrame p // c.val∈coordinatePlaneSlice p a δ} ≃ coordinatePlaneSlice p a δ where
  toFun c := ⟨c.val.val,c.prop⟩
  invFun c := ⟨⟨c.val,coordinatePlaneSlice_subset p a δ c.prop⟩,c.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coordinatePlaneSlice_card (p a : Point) (hap : dot a.val p.val=0) (δ : Bit) :
    Nat.card (coordinatePlaneSlice p a δ)=2 := by
  have hc := coordinateRow_predicate_card p (fun c => c∈coordinatePlaneSlice p a δ)
  rw [Nat.card_congr (Equiv.subtypeEquivRight (coordinatePlaneSlice_mem p a hap δ)),
    Nat.card_congr (coordinateRowSliceEquiv p a δ)] at hc
  have hd : Nat.card {x : E // dot a.val x=δ}=4 := by
    rw [Nat.card_eq_fintype_card]
    obtain ⟨r,rfl⟩ := rowLabel_bijective.2 a
    have cert : ∀r : Fin 7,∀b : Bit,Fintype.card {x : E // dot (rowLabel r).val x=b}=4 := by decide +kernel
    exact cert r δ
  rw [hd] at hc
  omega

def coordinatePlaneQuartet (p q a : Point) (δ ε : Bit) : Set MinimalCross :=
  coordinatePlaneSlice p a δ ∪ coordinatePlaneSlice q a ε

theorem coordinatePlaneQuartet_card (p q a : Point) (hpq : p≠q)
    (hap : dot a.val p.val=0) (haq : dot a.val q.val=0) (δ ε : Bit) :
    (coordinatePlaneQuartet p q a δ ε).ncard=4 := by
  have hd : Disjoint (coordinatePlaneSlice p a δ) (coordinatePlaneSlice q a ε) :=
    (coordinateRowFrame_disjoint hpq).mono (coordinatePlaneSlice_subset p a δ) (coordinatePlaneSlice_subset q a ε)
  rw [coordinatePlaneQuartet,Set.ncard_union_eq hd]
  have h1 := coordinatePlaneSlice_card p a hap δ
  have h2 := coordinatePlaneSlice_card q a haq ε
  change Nat.card (coordinatePlaneSlice p a δ)+Nat.card (coordinatePlaneSlice q a ε)=4
  rw [h1,h2]

theorem coordinatePlaneQuartet_subset (p q a : Point) (δ ε : Bit) :
    coordinatePlaneQuartet p q a δ ε⊆coordinateFrame := by
  rintro c (h|h)
  · exact coordinateRowFrame_subset p (coordinatePlaneSlice_subset p a δ h)
  · exact coordinateRowFrame_subset q (coordinatePlaneSlice_subset q a ε h)

theorem coordinatePlaneQuartet_pairwise (p q a : Point) (δ ε : Bit) :
    (coordinatePlaneQuartet p q a δ ε).Pairwise CrossOrthogonal := by
  intro x hx y hy hxy
  exact (coordinateFrame_orthogonal_iff _ _ (coordinatePlaneQuartet_subset p q a δ ε hx)
    (coordinatePlaneQuartet_subset p q a δ ε hy)).mpr hxy

end Atlas.Rudvalis
