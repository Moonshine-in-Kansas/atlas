import Atlas.Rudvalis.FourCoupleProjection
import Atlas.Rudvalis.CoupleSupportTranslations
import Atlas.Rudvalis.CoupleFourFibre

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def coupleFourStep (z : Fin 3×E) : Fin 3×E :=
  (coupleFourTransportForm z.1,coupleFourTransportParameters 1 z.1 z.2)

theorem coupleFourStep_state (z : Fin 3×E) :
    coupleFourState (coupleFourStep z).1 (coupleFourStep z).2=
      coupleSixStatePermutation 1 (coupleFourState z.1 z.2) :=
  coupleFour_six_state_action 1 z.1 z.2

theorem coupleFourIterate_state (n : ℕ) (z : Fin 3×E) :
    coupleFourState ((coupleFourStep^[n]) z).1 ((coupleFourStep^[n]) z).2=
      ((coupleSixStatePermutation 1)^[n]) (coupleFourState z.1 z.2) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',coupleFourStep_state,ih]

theorem coupleFourState_eq_iff (a b : Fin 3) (m n : E) :
    coupleFourState a m=coupleFourState b n ↔ a=b ∧ coupleFourParity a m=coupleFourParity b n := by
  decide +kernel +revert

theorem coupleFourState_first (a : Fin 3) (m : E) :
    (coupleFourState a m).val<2 ↔ a=0 := by decide +kernel +revert

theorem coupleBeta_reduce_iterate (n : ℕ) (z : Fin 3×E) (w : QuaternaryWord)
    (hw : reduce w=coupleFourSupport z.1 z.2) :
    reduce (monomialHom (coupleCodeBeta^n).val w)=
      coupleFourSupport ((coupleFourStep^[n]) z).1 ((coupleFourStep^[n]) z).2 := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    rw [pow_succ',Subgroup.coe_mul,map_mul]
    change reduce (monomialAction coupleCodeBeta.val (monomialHom (coupleCodeBeta^n).val w))=_
    rw [monomialAction_reduce,ih,Function.iterate_succ_apply']
    exact coupleFourSupport_action 1 _ _

theorem coupleBeta_pow_fix (n : ℕ) :
    coupleCodeBeta^n • localReferenceCross=localReferenceCross ∧
      coupleCodeBeta^n • referenceSecondCross=referenceSecondCross := by
  have hf := coupleCodeBeta_fixes_reference
  change coupleCodeBeta • localReferenceCross=localReferenceCross ∧
    coupleCodeBeta • referenceSecondCross=referenceSecondCross at hf
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ',mul_smul,ih.1,ih.2,hf.1,hf.2, and_self]

theorem coupleFour_same_class_support_orbit (a b : Fin 3) (m n : E)
    (hab : a=0 ↔ b=0) (w : QuaternaryWord) (hw : reduce w=coupleFourSupport a m) :
    ∃g : codeGroup,g • localReferenceCross=localReferenceCross ∧
      g • referenceSecondCross=referenceSecondCross ∧
      reduce (monomialHom g.val w)=coupleFourSupport b n := by
  have hs : (coupleFourState a m).val<2 ↔ (coupleFourState b n).val<2 := by
    rw [coupleFourState_first,coupleFourState_first]; exact hab
  obtain ⟨j,hj⟩ := coupleSixState_beta_connected _ _ hs
  let z := (coupleFourStep^[j.val]) (a,m)
  have hz : coupleFourState z.1 z.2=coupleFourState b n := (coupleFourIterate_state j.val (a,m)).trans hj
  obtain ⟨hzb,hze⟩ := (coupleFourState_eq_iff _ _ _ _).mp hz
  have hze' : coupleFourParity b z.2=coupleFourParity b n := by simpa only [hzb] using hze
  obtain ⟨B,hB,htrans⟩ := coupleFour_equal_parity_translation b z.2 n hze'
  obtain ⟨g,hg⟩ := codePermutationHom_surjective ⟨coordinateTranslation B,coordinateTranslation_mem B⟩
  have hgr : g.val.right=coordinateTranslation B := congrArg Subtype.val hg
  have hfix (x : E) : g • coordinateCross (rowLabel 0,x)=coordinateCross (rowLabel 0,x) := by
    rw [coordinateCross_action,hgr]
    change coordinateCross (rowLabel 0,x+matrixAt B (rowLabel 0).val)=_
    rw [hB,add_zero]
  refine ⟨g*coupleCodeBeta^j.val,?_,?_,?_⟩
  · rw [mul_smul,(coupleBeta_pow_fix j.val).1,localReferenceCross_eq]; exact hfix 0
  · rw [mul_smul,(coupleBeta_pow_fix j.val).2,referenceSecondCross_eq]; exact hfix _
  · rw [Subgroup.coe_mul,map_mul]
    change reduce (monomialAction g.val (monomialHom (coupleCodeBeta^j.val).val w))=_
    rw [monomialAction_reduce,hgr,coupleBeta_reduce_iterate j.val (a,m) w hw]
    change coupleFourSupport z.1 z.2 ∘ (coordinateTranslation B).symm=_
    rw [hzb]
    exact htrans.symm

end Atlas.Rudvalis
