import Atlas.Rudvalis.FourLocalSupportOrbit

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable abbrev FourLocalStabilizer := MulAction.stabilizer codeGroup (coordinateCross (originalCoordinateEquiv (0,1)))

theorem fourLocal_signed_fibre_orbit (w : SignedLift quaternaryCode fourPlaneSeedResidue) :
    ∃g : FourLocalStabilizer,monomialHom g.val.val (quaternarySeed (3,0,0,0))=w.val.val :=
  fourLocal_fibre_transitive ((minimumSignedLiftEquiv fourPlaneSeedResidue fourPlaneSeedResidue_weight).symm w)

theorem fourLocal_transported_word_orbit (g : FourLocalStabilizer)
    (w : SignedLift quaternaryCode (fourPlaneSeedResidue ∘ g.val.val.right.symm)) :
    ∃h : FourLocalStabilizer,monomialHom h.val.val (quaternarySeed (3,0,0,0))=w.val.val := by
  let e := signedLiftActionEquiv g.val fourPlaneSeedResidue
  obtain ⟨h,hh⟩ := fourLocal_signed_fibre_orbit (e.symm w)
  refine ⟨g*h,?_⟩
  change monomialHom (g.val.val*h.val.val) _=w.val.val
  rw [map_mul]
  change monomialHom g.val.val (monomialHom h.val.val _)=w.val.val
  rw [hh]
  exact congrArg (fun u => u.val.val) (e.apply_symm_apply w)

theorem fourLocal_fixed_label_word_orbit (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (h16 : euclideanWeight w=16) (δ : Point → Bit)
    (hδ : ∀p,dot (binaryLabel 1) p.val=0 → δ p=0) (hs : (∑p,δ p)=1)
    (hr : reduce w=binaryNormalMap (δ,outerMatrix (binaryLabel 1) (binaryLabel 1),0)) :
    ∃g : FourLocalStabilizer,monomialHom g.val.val (quaternarySeed (3,0,0,0))=w := by
  obtain ⟨g,hg⟩ := fourLocal_fixed_label_support_orbit δ hδ hs
  change reduce (monomialAction g.val.val (quaternarySeed (3,0,0,0)))=_ at hg
  rw [monomialAction_reduce,fourthSeed_residue] at hg
  exact fourLocal_transported_word_orbit g
    ⟨⟨w,hw⟩,hr.trans hg.symm,quaternary_minimum_no_twos w hw h16⟩

end Atlas.Rudvalis
