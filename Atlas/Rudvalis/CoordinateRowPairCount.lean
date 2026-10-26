import Atlas.Rudvalis.CoordinateCrossRows

namespace Atlas.Rudvalis

/-- Splitting the eight real coordinates into a representative and its Gaussian partner. -/
noncomputable def coordinatePairSplit (p : Point) (k : Fin 3) (hp : p.val k=1) :
    E ≃ {x : E // x k=0} × Bit where
  toFun x := (⟨x+x k • p.val,by
    change x k+x k*p.val k=0
    rw [hp,mul_one,CharTwo.add_self_eq_zero]⟩,x k)
  invFun y := y.1.val+y.2 • p.val
  left_inv x := by
    change (x+x k • p.val)+x k • p.val=x
    rw [add_assoc,vector_add_self,add_zero]
  right_inv y := by
    rcases y with ⟨⟨x,hx⟩,b⟩
    have hk : (x+b • p.val) k=b := by
      change x k+b*p.val k=b
      rw [hx,hp,mul_one,zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change (x+b • p.val)+(x+b • p.val) k • p.val=x
      rw [hk,add_assoc,vector_add_self,add_zero]
    · exact hk

theorem coordinateCross_smul_partner (p : Point) (x : E) (b : Bit) :
    coordinateCross (p,x+b • p.val)=coordinateCross (p,x) := by
  rcases Atlas.Codes.bit_cases b with rfl|rfl
  · rw [zero_smul,add_zero]
  · rw [one_smul]
    simpa only [codeI_coordinate] using coordinateCross_I (p,x)

/-- Every predicate on coordinate crosses has exactly two real representatives in each row. -/
theorem coordinateRow_predicate_card (p : Point) (P : MinimalCross→Prop) :
    Nat.card {x : E // P (coordinateCross (p,x))}=
      2*Nat.card {c : coordinateRowFrame p // P c.val} := by
  classical
  obtain ⟨k,hk⟩ := point_has_one p
  let e := coordinatePairSplit p k hk
  let f : {x : E // P (coordinateCross (p,x))} ≃
      {y : {x : E // x k=0} × Bit // P (coordinateCross (p,y.1.val))} :=
    Equiv.subtypeEquiv e (fun x => by
      change P (coordinateCross (p,x)) ↔ P (coordinateCross (p,x+x k • p.val))
      rw [coordinateCross_smul_partner])
  let h : {y : {x : E // x k=0} × Bit // P (coordinateCross (p,y.1.val))} ≃
      {x : {x : E // x k=0} // P (coordinateCross (p,x.val))} × Bit :=
    { toFun := fun y => (⟨y.val.1,y.prop⟩,y.val.2)
      invFun := fun y => ⟨(y.1.val,y.2),y.1.prop⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  let j : {x : {x : E // x k=0} // P (coordinateCross (p,x.val))} ≃
      {c : coordinateRowFrame p // P c.val} :=
    Equiv.subtypeEquiv (coordinateRowParamEquiv p k hk) (fun _ => Iff.rfl)
  rw [Nat.card_congr f,Nat.card_congr h,Nat.card_prod,Nat.card_congr j]
  have hb : Nat.card Bit=2 := by simp [Nat.card_eq_fintype_card,Bit,ZMod.card]
  rw [hb,Nat.mul_comm]

end Atlas.Rudvalis
