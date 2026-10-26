import Atlas.Rudvalis.ReferenceLinearLifts

namespace Atlas.Rudvalis

 theorem fourCrossHasLabel_unique {a b : Point} {c : MinimalCross}
    (ha : FourCrossHasLabel a c) (hb : FourCrossHasLabel b c) : a=b := by
  have hu : ∀a b : Point,(∀p : Point,dot a.val p.val=0 ↔ dot b.val p.val=0) ↔ a=b := by
    decide +kernel
  exact (hu a b).mp (fun p=>(ha p 0).symm.trans (hb p 0))

 theorem fourCrossHasLabel_transport (g : codeGroup) (a b : Point)
    (hg : ∀v : E,dot b.val (codeBlockLinearHom g v)=dot a.val v)
    (c : MinimalCross) (hc : FourCrossHasLabel a c) : FourCrossHasLabel b (g • c) := by
  intro p x
  let z := g.val.right.symm (p,x)
  have hz : g.val.right z=(p,x) := g.val.right.apply_symm_apply _
  have hr : codeBlockLinearHom g z.1.val=p.val := by
    rw [codeBlockLinear_coordinates,hz]
  have he := crossOrthogonal_codeGroup g (coordinateCross z) c
  rw [coordinateCross_action,hz] at he
  exact he.trans ((hc z.1 z.2).trans (by rw [←hg,hr]))

 theorem fourCrossHasLabel_active (a : Point) (c : MinimalCross) (hc : FourCrossHasLabel a c)
    (hn : ¬CrossOrthogonal localReferenceCross c) : dot a.val (rowLabel 0).val=1 := by
  have h : dot a.val (rowLabel 0).val≠0 := by
    intro he
    apply hn
    rw [localReferenceCross_eq]
    exact (hc (rowLabel 0) 0).mpr he
  have hh : ∀k : Bit,k≠0 → k=1 := by decide
  exact hh _ h

 theorem codeReferenceStabilizer_active_forms (a b : Point)
    (ha : dot a.val (rowLabel 0).val=1) (hb : dot b.val (rowLabel 0).val=1) :
    ∃g : codeReferenceStabilizer,∀v : E,
      dot b.val (codeBlockLinearHom g.val v)=dot a.val v := by
  obtain ⟨g,hg⟩ := codeReferenceStabilizer_linear_lift
    (activeFormTransvection (rowLabel 0) a b ha hb)
    (activeFormTransvection_fixed (rowLabel 0) a b ha hb)
  exact ⟨g,fun v=>by rw [hg]; exact activeFormTransvection_dual _ _ _ _ _ v⟩

end Atlas.Rudvalis
