import Atlas.Rudvalis.HeavyPairTranslation
import Atlas.Rudvalis.HeavySignTransitivity

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem heavy_pair_signedLift_transitive (c p : Point) (hpc : p≠c)
    (v w : HeavyAvoidingPair c p 0)
    (a : SignedLift quaternaryCode (fixedHeavyWord c v.val))
    (b : SignedLift quaternaryCode (fixedHeavyWord c w.val)) :
    ∃g : codeGroup,g • coordinateCross (p,0)=coordinateCross (p,0) ∧
      monomialHom g.val a.val.val=b.val.val := by
  obtain ⟨A,hAp,hA⟩ := heavy_pair_fixing_translation c p hpc v w
  obtain ⟨g,hg⟩ := codePermutationHom_surjective (coordinateTranslationHom (Multiplicative.ofAdd A))
  have hgr : g.val.right=coordinateTranslation A := congrArg Subtype.val hg
  have hgs : g.val.right.symm=coordinateTranslation A := by rw [hgr]; rfl
  have hfix : g • coordinateCross (p,0)=coordinateCross (p,0) := by
    rw [coordinateCross_action,hgr]
    exact (translation_fixes_coordinateCross_iff A p 0).mpr hAp
  let a' : SignedLift quaternaryCode (fixedHeavyWord c w.val) :=
    ⟨⟨monomialHom g.val a.val.val,(g.prop _).mp a.val.prop⟩,by
      change reduce (monomialAction g.val a.val.val)=fixedHeavyWord c w.val
      rw [monomialAction_reduce,a.prop.1,hgs]
      exact hA.symm,monomial_no_twos g.val a.val.val a.prop.2⟩
  have hd : hasNonzeroQuadraticPart (fixedHeavyWord c w.val) :=
    ⟨(w.val.2.val,w.val.1.val,c.val),c.prop,rfl⟩
  obtain ⟨k,hkr,hk⟩ := heavy_signedLift_sign_transitive (fixedHeavyWord c w.val) hd w.val.2.prop a' b
  refine ⟨k*g,?_,?_⟩
  · rw [mul_smul,hfix]
    exact codeGroup_sign_fixes_coordinateCross k hkr (p,0)
  · change monomialHom (k.val*g.val) a.val.val=b.val.val
    rw [map_mul]
    exact hk

end Atlas.Rudvalis
