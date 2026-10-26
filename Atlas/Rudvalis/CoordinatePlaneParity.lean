import Atlas.Rudvalis.CoordinatePlaneSlices

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/- The local calculation concerns one eight-position row, not a group permutation certificate. -/
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 16384 in
theorem quadratic_plane_pair_parity (p a : Point) (hap : dot a.val p.val=0)
    (c b : E) (hc : c≠0) (ε δ : Bit)
    (hw : blockWeight ε b c=if p.val=c then 4 else 2) :
    (Finset.univ.filter (fun x : E => dot a.val x=δ ∧
      ε+dot b x+quadratic c x=0 ∧ ε+dot b (x+p.val)+quadratic c (x+p.val)=0)).card % 4=
      if dot a.val c=0 then 0 else 2 := by
  decide +kernel +revert

theorem coordinatePlane_predicate_card (p a : Point) (hap : dot a.val p.val=0) (δ : Bit)
    (P : MinimalCross→Prop) :
    Nat.card {x : E // dot a.val x=δ ∧ P (coordinateCross (p,x))}=
      2*Nat.card {c : coordinatePlaneSlice p a δ // P c.val} := by
  have h := coordinateRow_predicate_card p (fun c => c∈coordinatePlaneSlice p a δ ∧ P c)
  have he (x : E) : (coordinateCross (p,x)∈coordinatePlaneSlice p a δ ∧ P (coordinateCross (p,x))) ↔
      dot a.val x=δ ∧ P (coordinateCross (p,x)) := by rw [coordinatePlaneSlice_mem p a hap]
  let e : {c : coordinateRowFrame p // c.val∈coordinatePlaneSlice p a δ ∧ P c.val} ≃
      {c : coordinatePlaneSlice p a δ // P c.val} :=
    { toFun := fun c => ⟨⟨c.val.val,c.prop.1⟩,c.prop.2⟩
      invFun := fun c => ⟨⟨c.val.val,coordinatePlaneSlice_subset p a δ c.val.prop⟩,c.val.prop,c.prop⟩
      left_inv := by intro c; rfl
      right_inv := by intro c; rfl }
  rw [Nat.card_congr (Equiv.subtypeEquivRight he),Nat.card_congr e] at h
  exact h

end Atlas.Rudvalis
