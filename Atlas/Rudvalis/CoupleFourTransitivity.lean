import Atlas.Rudvalis.CoupleFourSupportOrbit

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

 theorem coupleFourSupport_reference_zero (a : Fin 3) (m x : E) :
    coupleFourSupport a m (rowLabel 0,x)=0 := by
  change coupleFourConstants a m (rowLabel 0)+
    dot (matrixAt (outerMatrix (coupleFourForm a) (coupleFourForm a)) (rowLabel 0).val) x+
    theta (rowLabel 0) 0 x=0
  have hz : dot (coupleFourForm a) (rowLabel 0).val=0 := by decide +kernel +revert
  simp only [matrixAt_outer,hz,zero_smul,theta_zero_parameter,add_zero]
  simpa [dot] using (coupleFourConstants_valid a m).1 (rowLabel 0) hz

theorem fourCouple_word_parameters (w : FourMinimumWords)
    (hz : ∀x,reduce w.val.val (rowLabel 0,x)=0) :
    ∃a : Fin 3,∃m : E,reduce w.val.val=coupleFourSupport a m := by
  obtain ⟨a,ε,hr,hε,hs⟩ := w.prop.2
  have ha : dot a.val (rowLabel 0).val=0 := by
    have h := fourNormal_pair ε a.val (rowLabel 0) 0
    rw [←hr,hz,hz,zero_add] at h
    exact h.symm
  have hc : ∀a : Point,dot a.val (rowLabel 0).val=0 → ∃i : Fin 3,a.val=coupleFourForm i := by
    decide +kernel
  obtain ⟨i,hi⟩ := hc a ha
  rw [hi] at hr hε
  obtain ⟨m,hm⟩ := coupleFourConstants_exhaustive i ε hε hs
  exact ⟨i,m,by simpa only [hm,coupleFourSupport] using hr⟩

theorem fourCouple_same_class_words (a b : Fin 3) (m n : E)
    (hab : a=0 ↔ b=0) (v w : QuaternaryWord)
    (hv : v∈quaternaryCode) (hw : w∈quaternaryCode)
    (hv16 : euclideanWeight v=16) (hw16 : euclideanWeight w=16)
    (hrv : reduce v=coupleFourSupport a m) (hrw : reduce w=coupleFourSupport b n) :
    ∃g : codeGroup,g • localReferenceCross=localReferenceCross ∧
      g • referenceSecondCross=referenceSecondCross ∧ monomialHom g.val v=w := by
  obtain ⟨g,hgx,hgy,hgr⟩ := coupleFour_same_class_support_orbit a b m n hab v hrv
  let u := monomialHom g.val v
  have hu : u∈quaternaryCode := (g.prop v).mp hv
  have hu16 : euclideanWeight u=16 := (monomial_euclideanWeight _ _).trans hv16
  have hur : reduce u=coupleFourSupport b n := hgr
  have huf : admissibleFourSupport (reduce u) := hur.symm ▸ coupleFourSupport_admissible b n
  have huz : ∀x,reduce u (rowLabel 0,x)=0 := by
    intro x; rw [hur]; exact coupleFourSupport_reference_zero b n x
  obtain ⟨h,hh,hact⟩ := fourCouple_same_residue_transitive u w hu hw hu16 hw16 huf huz (hur.trans hrw.symm)
  refine ⟨h*g,?_,?_,?_⟩
  · rw [mul_smul,hgx,localReferenceCross_eq]; exact hh 0
  · rw [mul_smul,hgy,referenceSecondCross_eq]; exact hh _
  · change monomialHom (h.val*g.val) v=w
    rw [map_mul]
    exact hact

 theorem fourSupportNormal_couple (a : Fin 3) (m : E) :
    fourSupportNormal ⟨coupleFourSupport a m,coupleFourSupport_admissible a m⟩=
      ⟨coupleFourForm a,coupleFourForm_ne_zero a⟩ := by
  let aa : Point := ⟨coupleFourForm a,coupleFourForm_ne_zero a⟩
  let ε : OddActiveConstants aa :=
    ⟨⟨coupleFourConstants a m,(coupleFourConstants_valid a m).1⟩,(coupleFourConstants_valid a m).2⟩
  have h : fourSupportEquiv ⟨aa,ε⟩=⟨coupleFourSupport a m,coupleFourSupport_admissible a m⟩ := rfl
  unfold fourSupportNormal
  rw [←h,Equiv.symm_apply_apply]

 theorem fourCouple_parameter_energy (w : FourMinimumWords) (a : Fin 3) (m : E)
    (hr : reduce w.val.val=coupleFourSupport a m) :
    coordinateRowEnergy referenceDozenRows (minimumWordShellLift (fourMinimumWord w)).val.val=
      if a=0 then 0 else 2 := by
  rw [fourWord_energy]
  have he : (⟨reduce w.val.val,w.prop.2⟩ : {d : BinaryWord // admissibleFourSupport d})=
      ⟨coupleFourSupport a m,coupleFourSupport_admissible a m⟩ := Subtype.ext hr
  rw [he,fourSupportNormal_couple]
  have hh : fourSelectedRows ⟨coupleFourForm a,coupleFourForm_ne_zero a⟩=
      if a=0 then 0 else 2 := by
    have hall : ∀a : Fin 3,fourSelectedRows ⟨coupleFourForm a,coupleFourForm_ne_zero a⟩=
        if a=0 then 0 else 2 := by
      unfold fourSelectedRows referenceDozenRows
      decide +kernel
    exact hall a
  rw [hh]
  split_ifs <;> norm_num



 theorem fourCouple_shell_transitive (v w : fourShellPiece)
    (hv : ReferenceCoupleOrthogonal (minimalCross v.val))
    (hw : ReferenceCoupleOrthogonal (minimalCross w.val))
    (he : coordinateRowEnergy referenceDozenRows v.val.val.val=
      coordinateRowEnergy referenceDozenRows w.val.val.val) :
    ∃g : codeGroup,g • localReferenceCross=localReferenceCross ∧
      g • referenceSecondCross=referenceSecondCross ∧ g • v.val=w.val := by
  obtain ⟨a,ha⟩ := v.prop
  obtain ⟨b,hb⟩ := w.prop
  rw [←ha] at hv
  rw [←hb] at hw
  have hav := hv.1
  have hbw := hw.1
  rw [localReferenceCross_eq,fourWord_coordinate_orthogonal_iff] at hav hbw
  obtain ⟨i,m,him⟩ := fourCouple_word_parameters a hav
  obtain ⟨j,n,hjn⟩ := fourCouple_word_parameters b hbw
  have he' : (if i=0 then (0 : ℚ) else 2)=(if j=0 then (0 : ℚ) else 2) := by
    rw [←ha,←hb,fourCouple_parameter_energy a i m him,fourCouple_parameter_energy b j n hjn] at he
    exact he
  have hij : i=0 ↔ j=0 := by
    by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp_all
  obtain ⟨g,hgx,hgy,hg⟩ := fourCouple_same_class_words i j m n hij a.val.val b.val.val
    a.val.prop b.val.prop a.prop.1 b.prop.1 him hjn
  refine ⟨g,hgx,hgy,?_⟩
  rw [←ha,←hb,←minimumWordShellLift_equivariant]
  apply congrArg minimumWordShellLift
  exact Subtype.ext (Subtype.ext hg)

/-- Actual couple-stabilizer transitivity on each of the 64- and 128-cross four-block pieces. -/
theorem fourCouple_crosses_transitive (v w : FourBlockCrosses)
    (hv : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece v))
    (hw : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece w))
    (he : crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece v)=
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece w)) :
    ∃g : codeGroup,g • localReferenceCross=localReferenceCross ∧
      g • referenceSecondCross=referenceSecondCross ∧
      g • shellPieceCrossMap fourShellPiece v=shellPieceCrossMap fourShellPiece w := by
  induction v using Quotient.inductionOn with | h v =>
    induction w using Quotient.inductionOn with | h w =>
      obtain ⟨g,hgx,hgy,hg⟩ := fourCouple_shell_transitive v w hv hw he
      refine ⟨g,hgx,hgy,?_⟩
      change g • minimalCross v.val=minimalCross w.val
      rw [←minimalCross_smul,hg]

end Atlas.Rudvalis
