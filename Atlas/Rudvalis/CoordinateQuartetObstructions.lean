import Atlas.Rudvalis.CoordinateQuartetIncidence

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- Every nonzero Fano linear form is tested by an actual noncoordinate minimum cross. -/
theorem fourBlock_test_cross (a : Point) : ∃v : MinimalCross,v∉coordinateFrame ∧
    ∀p : Point,∀x : E,CrossOrthogonal v (coordinateCross (p,x)) ↔ dot a.val p.val=0 := by
  let t : FourSupportParameters := ⟨a,⟨activeParityOne a,activeParityOne_parity a⟩⟩
  let d := fourSupportEquiv t
  have hc : Nat.card (minimumLift d.val)=32 := four_minimum_fibre_card d.val d.prop
  have hn : Nonempty (minimumLift d.val) := (Nat.card_pos_iff.mp (by rw [hc]; decide)).1
  obtain ⟨w⟩ := hn
  let w' : FourMinimumWords := ⟨w.val,w.prop.1,w.prop.2.symm ▸ d.prop⟩
  refine ⟨minimalCross (minimumWordShellLift (fourMinimumWord w')),?_,?_⟩
  · intro h
    obtain ⟨i,hi⟩ := (minimalCross_mem_coordinateFrame _).mp h
    exact coordinateShellLift_ne_minimumWordShellLift i (fourMinimumWord w') hi
  · intro p x
    rw [crossOrthogonal_symm,fourWord_coordinate_orthogonal_iff]
    change (∀y : E,reduce w.val.val (p,y)=0) ↔ dot a.val p.val=0
    rw [w.prop.2]
    exact fourSupport_parameter_row_zero t p

/-- A linear form cannot pick out just one member of an intrinsic coordinate quartet. -/
theorem coordinateQuartet_no_single_linear_label (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (hF : Q⊆coordinateFrame) (a p : Point) (x : E)
    (hq : coordinateCross (p,x)∈Q) (ha : dot a.val p.val=1)
    (hrest : ∀z∈Q,z≠coordinateCross (p,x) →
      ∃r : Point,∃y : E,z=coordinateCross (r,y) ∧ dot a.val r.val=0) : False := by
  obtain ⟨v,hv,ht⟩ := fourBlock_test_cross a
  have hvo : v∉Q := by intro h; exact hv (hF h)
  have horth := hQ.2.2 v hvo (coordinateCross (p,x)) hq (by
    intro z hz hne
    obtain ⟨r,y,rfl,hr⟩ := hrest z hz hne
    exact (ht r y).mpr hr)
  have hzero := (ht p x).mp horth
  rw [ha] at hzero
  exact one_ne_zero hzero

/-- The forbidden (3,1) row pattern, stated without enumerating quartets. -/
theorem coordinateQuartet_not_three_one (p q : Point) (hpq : p≠q) (x : E)
    (Q : Set MinimalCross) (hQ : IsQuartet Q) (hq : coordinateCross (q,x)∈Q)
    (hrest : ∀z∈Q,z≠coordinateCross (q,x) → z∈coordinateRowFrame p) : False := by
  have sep : ∀p q : Point,p≠q → ∃a : Point,dot a.val p.val=0 ∧ dot a.val q.val=1 := by
    decide +kernel
  obtain ⟨a,hap,haq⟩ := sep p q hpq
  have hF : Q⊆coordinateFrame := by
    intro z hz
    by_cases he : z=coordinateCross (q,x)
    · rw [he]
      exact coordinateCross_mem _
    · exact coordinateRowFrame_subset p (hrest z hz he)
  apply coordinateQuartet_no_single_linear_label Q hQ hF a q x hq haq
  intro z hz hne
  obtain ⟨y,hy⟩ := hrest z hz hne
  exact ⟨p,y,hy.symm,hap⟩

end Atlas.Rudvalis
