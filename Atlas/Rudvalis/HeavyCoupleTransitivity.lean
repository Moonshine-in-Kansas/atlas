import Atlas.Rudvalis.HeavyCoupleFibre
import Atlas.Rudvalis.HeavyBlockTransport
import Atlas.Rudvalis.HeavyLocalOrbitSet
import Atlas.Rudvalis.CoupleFusionGroup

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem heavyCoupleWord_action (g : codeCoupleStabilizer) (w : HeavyCoupleWords) :
    ∃u : HeavyCoupleWords,monomialHom g.val.val w.val.val.val=u.val.val.val := by
  obtain ⟨u,hu⟩ := heavyWord_action_exists g.val w.val
  have he : g.val • heavyMinimumWord w.val=heavyMinimumWord u :=
    Subtype.ext (Subtype.ext hu)
  have hx : g.val • minimalCross (minimumWordShellLift (heavyMinimumWord w.val))=
      minimalCross (minimumWordShellLift (heavyMinimumWord u)) := by
    rw [←minimalCross_smul,←minimumWordShellLift_equivariant,he]
  have hw := (heavyWord_reference_couple_iff w.val).mpr w.prop
  have h0 := (crossOrthogonal_codeGroup g.val localReferenceCross _).mpr hw.1
  have h2 := (crossOrthogonal_codeGroup g.val referenceSecondCross _).mpr hw.2
  rw [g.prop.1,hx] at h0
  rw [g.prop.2,hx] at h2
  exact ⟨⟨u,(heavyWord_reference_couple_iff u).mp ⟨h0,h2⟩⟩,hu⟩

theorem heavyCoupleWord_parameters (w : HeavyCoupleWords) :
    ∃c : Point,∃a : HeavyAvoidingPair c (rowLabel 0) 0,
      HeavyCoupleLabel c ∧ reduce w.val.val.val=fixedHeavyWord c a.val := by
  obtain ⟨c,a,_,ha⟩ := heavyWord_avoiding_parameters (rowLabel 0) w.val w.prop.1
  refine ⟨c,a,(heavy_couple_second_pair_iff c a).mp ?_,ha⟩
  rw [←ha]
  exact w.prop.2

theorem heavyCouple_same_label_transitive (v w : HeavyCoupleWords) (c : Point)
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

theorem coupleBeta_fuses_heavy_labels (c d : Point) (hc : HeavyCoupleLabel c)
    (hd : HeavyCoupleLabel d) (hcd : c≠d) : codeRowImage coupleCodeBeta c=d := by
  obtain ⟨r,rfl⟩ := rowLabel_bijective.2 c
  obtain ⟨s,rfl⟩ := rowLabel_bijective.2 d
  rw [coupleCodeBeta_rowImage]
  have cert : ∀r s : Fin 7,HeavyCoupleLabel (rowLabel r) → HeavyCoupleLabel (rowLabel s) →
      rowLabel r≠rowLabel s → rowLabel (coupleBetaRow r)=rowLabel s := by
    unfold HeavyCoupleLabel
    decide +kernel
  exact cert r s hc hd hcd

/-- Both heavy labels and every signed lift fuse under the actual pointwise couple stabilizer. -/
theorem heavyCoupleWord_transitive (v w : HeavyCoupleWords) :
    ∃g : codeCoupleStabilizer,monomialHom g.val.val v.val.val.val=w.val.val.val := by
  classical
  obtain ⟨c,a,hc,ha⟩ := heavyCoupleWord_parameters v
  obtain ⟨d,b,hd,hb⟩ := heavyCoupleWord_parameters w
  by_cases hcd : c=d
  · subst d
    exact heavyCouple_same_label_transitive v w c a b ha hb
  · let beta : codeCoupleStabilizer := ⟨coupleCodeBeta,coupleCodeBeta_fixes_reference⟩
    obtain ⟨u,hu⟩ := heavyCoupleWord_action beta v
    obtain ⟨e,f,_,hf⟩ := heavyCoupleWord_parameters u
    have he := heavyWord_label_transport coupleCodeBeta v.val u.val c e a.val f.val ha hf hu
    rw [coupleBeta_fuses_heavy_labels c d hc hd hcd] at he
    subst e
    obtain ⟨g,hg⟩ := heavyCouple_same_label_transitive u w d f b hf hb
    refine ⟨g*beta,?_⟩
    simp only [Subgroup.coe_mul,map_mul,LinearEquiv.mul_apply,hu,hg]

/-- Transitivity on the actual 512 heavy crosses perpendicular to the reference couple. -/
theorem heavyCross_couple_stabilizer_transitive (a b : HeavyCrosses)
    (ha : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece a))
    (hb : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece b)) :
    ∃g : codeCoupleStabilizer,g.val • shellPieceCrossMap heavyShellPiece a=
      shellPieceCrossMap heavyShellPiece b := by
  obtain ⟨v,hv⟩ := heavyCross_rep a
  obtain ⟨w,hw⟩ := heavyCross_rep b
  have hv' := (heavyWord_reference_couple_iff v).mp (hv ▸ ha)
  have hw' := (heavyWord_reference_couple_iff w).mp (hw ▸ hb)
  obtain ⟨g,hg⟩ := heavyCoupleWord_transitive ⟨v,hv'⟩ ⟨w,hw'⟩
  refine ⟨g,?_⟩
  have he : g.val • heavyMinimumWord v=heavyMinimumWord w := Subtype.ext (Subtype.ext hg)
  rw [hv,hw,←minimalCross_smul,←minimumWordShellLift_equivariant,he]

end Atlas.Rudvalis
