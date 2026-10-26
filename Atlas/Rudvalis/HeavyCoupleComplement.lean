import Atlas.Rudvalis.HeavyCoupleOrbitSet

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

abbrev HeavySemiCoupleWords := {w : HeavyMinimumWords //
  (reduce w.val.val (rowLabel 0,0)=0 ∧ reduce w.val.val (rowLabel 0,0+(rowLabel 0).val)=0) ∧
  ¬(reduce w.val.val (rowLabel 0,binaryLabel 2)=0 ∧
    reduce w.val.val (rowLabel 0,binaryLabel 2+(rowLabel 0).val)=0)}

def ReferenceCoupleSemiOrthogonal (c : MinimalCross) : Prop :=
  CrossOrthogonal localReferenceCross c ∧ ¬CrossOrthogonal referenceSecondCross c

theorem heavyWord_reference_semi_couple_iff (w : HeavyMinimumWords) :
    ReferenceCoupleSemiOrthogonal (minimalCross (minimumWordShellLift (heavyMinimumWord w))) ↔
      ((reduce w.val.val (rowLabel 0,0)=0 ∧ reduce w.val.val (rowLabel 0,0+(rowLabel 0).val)=0) ∧
      ¬(reduce w.val.val (rowLabel 0,binaryLabel 2)=0 ∧
        reduce w.val.val (rowLabel 0,binaryLabel 2+(rowLabel 0).val)=0)) := by
  rw [ReferenceCoupleSemiOrthogonal,localReferenceCross_eq,referenceSecondCross_eq,
    heavyWord_coordinate_orthogonal_iff,heavyWord_coordinate_orthogonal_iff]

theorem heavySemiCoupleWord_parameters (w : HeavySemiCoupleWords) :
    ∃c : Point,∃a : HeavyAvoidingPair c (rowLabel 0) 0,
      ¬HeavyCoupleLabel c ∧ reduce w.val.val.val=fixedHeavyWord c a.val := by
  obtain ⟨c,a,_,ha⟩ := heavyWord_avoiding_parameters (rowLabel 0) w.val w.prop.1
  refine ⟨c,a,?_,ha⟩
  intro hc
  have h := (heavy_couple_second_pair_iff c a).mpr hc
  rw [←ha] at h
  exact w.prop.2 h

theorem codeRowImage_mul (g h : codeGroup) (p : Point) :
    codeRowImage (g*h) p=codeRowImage g (codeRowImage h p) := by
  change binaryBlockHom (codePermutationHom (g*h)) p=
    binaryBlockHom (codePermutationHom g) (binaryBlockHom (codePermutationHom h) p)
  rw [map_mul,map_mul]
  rfl

theorem codeRowImage_one (p : Point) : codeRowImage 1 p=p := by
  change binaryBlockHom (codePermutationHom 1) p=p
  rw [map_one,map_one]
  rfl

theorem coupleCodeBeta_pow_rowImage (n : ℕ) (r : Fin 7) :
    codeRowImage (coupleCodeBeta^n) (rowLabel r)=rowLabel ((coupleBetaRow^[n]) r) := by
  induction n with
  | zero => simp only [pow_zero,codeRowImage_one,Function.iterate_zero, id_eq]
  | succ n ih =>
    rw [pow_succ',codeRowImage_mul,ih,coupleCodeBeta_rowImage,Function.iterate_succ_apply']

theorem coupleBeta_fuses_other_heavy_labels (c d : Point) (hc : ¬HeavyCoupleLabel c)
    (hd : ¬HeavyCoupleLabel d) (hpc : rowLabel 0≠c) (hpd : rowLabel 0≠d) :
    ∃n : ℕ,codeRowImage (coupleCodeBeta^n) c=d := by
  obtain ⟨r,rfl⟩ := rowLabel_bijective.2 c
  obtain ⟨s,rfl⟩ := rowLabel_bijective.2 d
  have cert : ∀r s : Fin 7,¬HeavyCoupleLabel (rowLabel r) → ¬HeavyCoupleLabel (rowLabel s) →
      rowLabel 0≠rowLabel r → rowLabel 0≠rowLabel s →
      ∃n : Fin 4,(coupleBetaRow^[n.val]) r=s := by
    unfold HeavyCoupleLabel
    decide +kernel
  obtain ⟨n,hn⟩ := cert r s hc hd hpc hpd
  exact ⟨n.val,by rw [coupleCodeBeta_pow_rowImage,hn]⟩

theorem heavySemiCoupleWord_action (g : codeCoupleStabilizer) (w : HeavySemiCoupleWords) :
    ∃u : HeavySemiCoupleWords,monomialHom g.val.val w.val.val.val=u.val.val.val := by
  obtain ⟨u,hu⟩ := heavyWord_action_exists g.val w.val
  have he : g.val • heavyMinimumWord w.val=heavyMinimumWord u :=
    Subtype.ext (Subtype.ext hu)
  have hx : g.val • minimalCross (minimumWordShellLift (heavyMinimumWord w.val))=
      minimalCross (minimumWordShellLift (heavyMinimumWord u)) := by
    rw [←minimalCross_smul,←minimumWordShellLift_equivariant,he]
  have hw := (heavyWord_reference_semi_couple_iff w.val).mpr w.prop
  have h0 := (crossOrthogonal_codeGroup g.val localReferenceCross _).mpr hw.1
  have h2 := (crossOrthogonal_codeGroup g.val referenceSecondCross _).not.mpr hw.2
  rw [g.prop.1,hx] at h0
  rw [g.prop.2,hx] at h2
  exact ⟨⟨u,(heavyWord_reference_semi_couple_iff u).mp ⟨h0,h2⟩⟩,hu⟩

theorem heavySemiCouple_same_label_transitive (v w : HeavySemiCoupleWords) (c : Point)
    (a b : HeavyAvoidingPair c (rowLabel 0) 0)
    (hv : reduce v.val.val.val=fixedHeavyWord c a.val)
    (hw : reduce w.val.val.val=fixedHeavyWord c b.val) :
    ∃g : codeCoupleStabilizer,monomialHom g.val.val v.val.val.val=w.val.val.val := by
  let v' : SignedLift quaternaryCode (fixedHeavyWord c a.val) :=
    ⟨v.val.val,hv,quaternary_minimum_no_twos _ v.val.val.prop v.val.prop.1⟩
  let w' : SignedLift quaternaryCode (fixedHeavyWord c b.val) :=
    ⟨w.val.val,hw,quaternary_minimum_no_twos _ w.val.val.prop w.val.prop.1⟩
  obtain ⟨g,hg,hvw⟩ := heavy_pair_signedLift_row_transitive c (rowLabel 0)
    (heavyAvoidingPair_label_ne c _ a) a b v' w'
  refine ⟨⟨g,?_,?_⟩,hvw⟩
  · change g • localReferenceCross=localReferenceCross
    rw [localReferenceCross_eq]; exact hg 0
  · change g • referenceSecondCross=referenceSecondCross
    rw [referenceSecondCross_eq]; exact hg (binaryLabel 2)

theorem heavySemiCoupleWord_transitive (v w : HeavySemiCoupleWords) :
    ∃g : codeCoupleStabilizer,monomialHom g.val.val v.val.val.val=w.val.val.val := by
  obtain ⟨c,a,hc,ha⟩ := heavySemiCoupleWord_parameters v
  obtain ⟨d,b,hd,hb⟩ := heavySemiCoupleWord_parameters w
  obtain ⟨n,hn⟩ := coupleBeta_fuses_other_heavy_labels c d hc hd
    (heavyAvoidingPair_label_ne c _ a) (heavyAvoidingPair_label_ne d _ b)
  let beta : codeCoupleStabilizer := ⟨coupleCodeBeta,coupleCodeBeta_fixes_reference⟩
  obtain ⟨u,hu⟩ := heavySemiCoupleWord_action (beta^n) v
  obtain ⟨e,f,_,hf⟩ := heavySemiCoupleWord_parameters u
  have he := heavyWord_label_transport (coupleCodeBeta^n) v.val u.val c e a.val f.val ha hf hu
  rw [hn] at he
  subst e
  obtain ⟨g,hg⟩ := heavySemiCouple_same_label_transitive u w d f b hf hb
  refine ⟨g*beta^n,?_⟩
  simp only [Subgroup.coe_mul,map_mul,LinearEquiv.mul_apply,hu,hg]

theorem heavyCross_semi_couple_stabilizer_transitive (a b : HeavyCrosses)
    (ha : ReferenceCoupleSemiOrthogonal (shellPieceCrossMap heavyShellPiece a))
    (hb : ReferenceCoupleSemiOrthogonal (shellPieceCrossMap heavyShellPiece b)) :
    ∃g : codeCoupleStabilizer,g.val • shellPieceCrossMap heavyShellPiece a=
      shellPieceCrossMap heavyShellPiece b := by
  obtain ⟨v,hv⟩ := heavyCross_rep a
  obtain ⟨w,hw⟩ := heavyCross_rep b
  have hv' := (heavyWord_reference_semi_couple_iff v).mp (hv ▸ ha)
  have hw' := (heavyWord_reference_semi_couple_iff w).mp (hw ▸ hb)
  obtain ⟨g,hg⟩ := heavySemiCoupleWord_transitive ⟨v,hv'⟩ ⟨w,hw'⟩
  refine ⟨g,?_⟩
  have he : g.val • heavyMinimumWord v=heavyMinimumWord w := Subtype.ext (Subtype.ext hg)
  rw [hv,hw,←minimalCross_smul,←minimumWordShellLift_equivariant,he]

end Atlas.Rudvalis
