import Atlas.Rudvalis.CoupleCoordinateOrbitSets

namespace Atlas.Rudvalis

private theorem reference_pair_eq (s : CoordinateRowPair) (p : Point) (hp : p≠rowLabel 0)
    (h0 : rowLabel 0∈s.val) (hps : p∈s.val) : s.val={rowLabel 0,p} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl|hq
    · exact h0
    · exact Finset.mem_singleton.mp hq ▸ hps
  · rw [s.prop]
    simp [Ne.symm hp]

 theorem referencePlane_unique_through_cross (v w : CoordinatePlaneQuartetParameters)
    (hv : ReferencePlaneParameters v) (hw : ReferencePlaneParameters w)
    (p : Point) (hp : p≠rowLabel 0) (x : E)
    (hxv : coordinateCross (p,x)∈coordinatePlaneQuartetFromParameters v)
    (hxw : coordinateCross (p,x)∈coordinatePlaneQuartetFromParameters w) : v=w := by
  have hpv : p∈v.1.val := (coordinatePlaneQuartetFromParameters_rows v p).mp ⟨_,hxv,x,rfl⟩
  have hpw : p∈w.1.val := (coordinatePlaneQuartetFromParameters_rows w p).mp ⟨_,hxw,x,rfl⟩
  have hs : v.1=w.1 := Subtype.ext
    ((reference_pair_eq v.1 p hp hv.choose hpv).trans (reference_pair_eq w.1 p hp hw.choose hpw).symm)
  rcases v with ⟨s,f⟩
  rcases w with ⟨t,h⟩
  dsimp only at hs
  subst t
  congr 1
  funext q
  have hq : q.val=rowLabel 0 ∨ q.val=p := by
    have h : q.val∈({rowLabel 0,p} : Finset Point) :=
      Finset.mem_of_subset (le_of_eq (reference_pair_eq s p hp hv.choose hpv)) q.prop
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  rcases hq with hq|hq
  · have he : q=⟨rowLabel 0,hv.choose⟩ := Subtype.ext hq
    rw [he]
    exact hv.choose_spec.2.trans hw.choose_spec.2.symm
  · have he : q=⟨p,hpv⟩ := Subtype.ext hq
    rw [he]
    exact ((coordinatePlaneQuartetFromParameters_mem s f ⟨p,hpv⟩ x).mp hxv).trans
      ((coordinatePlaneQuartetFromParameters_mem s h ⟨p,hpv⟩ x).mp hxw).symm

 theorem referenceCoordinateQuartet_unique_outside_row (Q R : Set MinimalCross)
    (hQ : IsQuartet Q) (hR : IsQuartet R) (hQF : Q⊆coordinateFrame) (hRF : R⊆coordinateFrame)
    (hcQ : referenceCouple⊆Q) (hcR : referenceCouple⊆R)
    (c : MinimalCross) (hc : c∉coordinateRowFrame (rowLabel 0)) (hcq : c∈Q) (hcr : c∈R) : Q=R := by
  obtain ⟨⟨p,x⟩,rfl⟩ := coordinateFrame_rep c (hQF hcq)
  have hp : p≠rowLabel 0 := by intro h; subst p; exact hc ⟨x,rfl⟩
  have plane (S : Set MinimalCross) (hS : IsQuartet S) (hSF : S⊆coordinateFrame)
      (hcS : referenceCouple⊆S) (hcs : coordinateCross (p,x)∈S) :
      ∃v : CoordinatePlaneQuartetParameters,S=coordinatePlaneQuartetFromParameters v := by
    obtain ⟨v,rfl⟩ := coordinateQuartet_classification S hS hSF
    cases v with
    | inl q =>
      have hq := referenceCouple_subset_row_iff q |>.mp hcS
      exact False.elim (hc (hq ▸ hcs))
    | inr v => exact ⟨v,rfl⟩
  obtain ⟨v,rfl⟩ := plane Q hQ hQF hcQ hcq
  obtain ⟨w,rfl⟩ := plane R hR hRF hcR hcr
  exact congrArg coordinatePlaneQuartetFromParameters
    (referencePlane_unique_through_cross v w ((referencePlaneParameters_iff v).mp hcQ)
      ((referencePlaneParameters_iff w).mp hcR) p hp x hcq hcr)



 theorem referenceCoordinateQuartet_outside_row (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (hne : Q≠coordinateRowFrame (rowLabel 0)) : ∃c∈Q,c∉coordinateRowFrame (rowLabel 0) := by
  classical
  by_contra hn
  push Not at hn
  apply hne
  apply Set.eq_of_subset_of_ncard_le hn
  · change Nat.card (coordinateRowFrame (rowLabel 0))≤Q.ncard
    rw [coordinateRowFrame_card,hQ.1]

/-- The four non-row coordinate quartets through the reference couple form one actual stabilizer orbit. -/
theorem referenceCoordinateQuartets_nonrow_transitive (Q R : Set MinimalCross)
    (hQ : IsQuartet Q) (hR : IsQuartet R) (hQF : Q⊆coordinateFrame) (hRF : R⊆coordinateFrame)
    (hcQ : referenceCouple⊆Q) (hcR : referenceCouple⊆R)
    (hneQ : Q≠coordinateRowFrame (rowLabel 0)) (hneR : R≠coordinateRowFrame (rowLabel 0)) :
    ∃g : codeCoupleStabilizer,(fun c : MinimalCross=>g.val • c) '' Q=R := by
  obtain ⟨c,hc,hcn⟩ := referenceCoordinateQuartet_outside_row Q hQ hneQ
  obtain ⟨d,hd,hdn⟩ := referenceCoordinateQuartet_outside_row R hR hneR
  have hcD : c∈referenceCoordinateDozen :=
    reference_quartet_coordinate_member_in_dozen Q hQ hcQ c hc (hQF hc)
  have hdD : d∈referenceCoordinateDozen :=
    reference_quartet_coordinate_member_in_dozen R hR hcR d hd (hRF hd)
  obtain ⟨g,hg⟩ := couple_coordinate_dozen_other_rows_transitive c d ⟨hcD,hcn⟩ ⟨hdD,hdn⟩
  refine ⟨g,?_⟩
  let S := (fun c : MinimalCross=>g.val • c) '' Q
  have hS : IsQuartet S := by
    simpa only [S,gaussianImage,codeGaussianHom_cross] using
      (isQuartet_gaussianImage (codeGaussianHom g.val) Q).mpr hQ
  have hSF : S⊆coordinateFrame := by
    rintro z ⟨w,hw,rfl⟩
    exact coordinateFrame_code_stable g.val w (hQF hw)
  have hcS : referenceCouple⊆S := by
    intro z hz
    refine ⟨z,hcQ hz,?_⟩
    rcases hz with rfl|rfl
    · exact g.prop.1
    · exact g.prop.2
  exact referenceCoordinateQuartet_unique_outside_row S R hS hR hSF hRF hcS hcR d hdn
    ⟨c,hc,hg⟩ hd

end Atlas.Rudvalis
