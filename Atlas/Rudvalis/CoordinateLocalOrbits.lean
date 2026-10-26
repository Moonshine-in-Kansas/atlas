import Atlas.Rudvalis.CoordinateCrossLocalAction
import Atlas.Rudvalis.CoordinateCrossStabilizer

namespace Atlas.Rudvalis

theorem coordinateCross_row_of_eq {i j : Coordinate}
    (h : coordinateCross i=coordinateCross j) : i.1=j.1 := by
  rcases (coordinateCross_eq_iff i j).mp h with h|h
  · exact congrArg Prod.fst h
  · simpa only [codeI_coordinate] using congrArg Prod.fst h

theorem coordinateCross_stabilizer_row (p : Point) (x : E)
    (g : MulAction.stabilizer codeGroup (coordinateCross (p,x))) :
    codeBlockLinearHom g.val p.val=p.val := by
  have h := g.prop
  change g.val • coordinateCross (p,x)=coordinateCross (p,x) at h
  rw [coordinateCross_action] at h
  rw [codeBlockLinear_coordinates g.val (p,x)]
  exact congrArg Subtype.val (coordinateCross_row_of_eq h)

theorem coordinateCross_stabilizer_row_mem (p : Point) (x : E)
    (g : MulAction.stabilizer codeGroup (coordinateCross (p,x)))
    (c : MinimalCross) (hc : c∈coordinateRowFrame p) :
    g • c∈coordinateRowFrame p := by
  obtain ⟨z,rfl⟩ := hc
  change g.val • coordinateCross (p,z)∈coordinateRowFrame p
  rw [coordinateCross_action]
  have hr : (g.val.val.right (p,z)).1=p := by
    apply Subtype.ext
    rw [←codeBlockLinear_coordinates,coordinateCross_stabilizer_row]
  refine ⟨(g.val.val.right (p,z)).2,?_⟩
  exact congrArg coordinateCross (Prod.ext hr.symm rfl)

theorem coordinateCross_same_row_orbit (p : Point) (x y : E)
    (hy : coordinateCross (p,y)≠coordinateCross (p,x)) :
    MulAction.orbit (MulAction.stabilizer codeGroup (coordinateCross (p,x))) (coordinateCross (p,y))=
      coordinateRowFrame p\{coordinateCross (p,x)} := by
  apply Set.ext
  intro c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    refine ⟨coordinateCross_stabilizer_row_mem p x g _ ⟨y,rfl⟩,?_⟩
    intro he
    have hg : g • coordinateCross (p,x)=coordinateCross (p,x) := g.prop
    exact hy (MulAction.injective g (he.trans hg.symm))
  · rintro ⟨⟨z,rfl⟩,hz⟩
    exact MulAction.mem_orbit_iff.mpr (coordinateCross_same_row_transitive p x y z hy hz)

theorem coordinateCross_same_row_orbit_card (p : Point) (x y : E)
    (hy : coordinateCross (p,y)≠coordinateCross (p,x)) :
    Nat.card (MulAction.orbit (MulAction.stabilizer codeGroup (coordinateCross (p,x)))
      (coordinateCross (p,y)))=3 := by
  rw [coordinateCross_same_row_orbit p x y hy]
  classical
  let e : ↥(coordinateRowFrame p\{coordinateCross (p,x)}) ≃
      {c : coordinateRowFrame p // CrossOrthogonal (coordinateCross (p,x)) c.val} :=
    { toFun := fun c => ⟨⟨c.val,c.prop.1⟩,
        (coordinateFrame_orthogonal_iff _ _ (coordinateCross_mem _) (coordinateRowFrame_subset p c.prop.1)).mpr
          (Ne.symm c.prop.2)⟩
      invFun := fun c => ⟨c.val.val,c.val.prop,by
        intro h
        exact crossOrthogonal_irrefl _ (h ▸ c.prop)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact coordinateRowFrame_orthogonal_card p ⟨coordinateCross (p,x),⟨x,rfl⟩⟩

theorem coordinate_same_row_pair_stabilizer_order (p : Point) (x y : E)
    (hy : coordinateCross (p,y)≠coordinateCross (p,x)) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer codeGroup (coordinateCross (p,x)))
      (coordinateCross (p,y)))=16384 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (MulAction.stabilizer codeGroup (coordinateCross (p,x))) (coordinateCross (p,y)))
  rw [Nat.card_prod,coordinateCross_same_row_orbit_card p x y hy,
    coordinateCross_stabilizer_order _ (coordinateCross_mem _)] at h
  omega

theorem coordinateCross_other_rows_orbit (p q : Point) (hpq : p≠q) (x y : E) :
    MulAction.orbit (MulAction.stabilizer codeGroup (coordinateCross (p,x))) (coordinateCross (q,y))=
      coordinateFrame\coordinateRowFrame p := by
  have hn : coordinateCross (q,y)∉coordinateRowFrame p := by
    rintro ⟨z,hz⟩
    exact hpq (coordinateCross_row_of_eq hz)
  apply Set.ext
  intro c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    refine ⟨coordinateFrame_code_stable g.val _ (coordinateCross_mem _),?_⟩
    intro h
    have ht := coordinateCross_stabilizer_row_mem p x g⁻¹ _ h
    exact hn (by simpa using ht)
  · rintro ⟨hc,hnc⟩
    obtain ⟨⟨r,z⟩,rfl⟩ := coordinateFrame_rep c hc
    have hpr : p≠r := by
      intro he
      subst r
      exact hnc ⟨z,rfl⟩
    exact MulAction.mem_orbit_iff.mpr (coordinateCross_other_rows_transitive p q r hpq hpr x y z)

theorem coordinateCross_other_rows_orbit_card (p q : Point) (hpq : p≠q) (x y : E) :
    Nat.card (MulAction.orbit (MulAction.stabilizer codeGroup (coordinateCross (p,x)))
      (coordinateCross (q,y)))=24 := by
  rw [coordinateCross_other_rows_orbit p q hpq x y]
  let e : ↥(coordinateFrame\coordinateRowFrame p) ≃
      {c : coordinateFrame // c.val∉coordinateRowFrame p} :=
    { toFun := fun c => ⟨⟨c.val,c.prop.1⟩,c.prop.2⟩
      invFun := fun c => ⟨c.val.val,c.val.prop,c.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact coordinateFrame_outside_row_card p

theorem coordinate_different_row_pair_stabilizer_order (p q : Point) (hpq : p≠q) (x y : E) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer codeGroup (coordinateCross (p,x)))
      (coordinateCross (q,y)))=2048 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (MulAction.stabilizer codeGroup (coordinateCross (p,x))) (coordinateCross (q,y)))
  rw [Nat.card_prod,coordinateCross_other_rows_orbit_card p q hpq x y,
    coordinateCross_stabilizer_order _ (coordinateCross_mem _)] at h
  omega

end Atlas.Rudvalis

