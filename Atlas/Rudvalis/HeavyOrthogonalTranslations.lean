import Atlas.Rudvalis.HeavyOrthogonalLocal
import Atlas.Rudvalis.FanoLinear

namespace Atlas.Rudvalis

noncomputable def fixedHeavyTranslate (c : Point) (A : BinaryMatrix) (v : FixedHeavyParameters c) :
    FixedHeavyParameters c := by
  let a := translatedParameters A (v.2.val,v.1.val,c.val)
  have hw : hammingNorm (binaryNormalMap a)=16 := by
    rw [binaryNormalMap_translation,binaryWord_weight_permute]
    exact v.2.prop
  exact ⟨⟨a.2.1,binaryNormalMap_quadratic_minimum_contraction a c.prop hw⟩,⟨a.1,hw⟩⟩

theorem fixedHeavyTranslate_word (c : Point) (A : BinaryMatrix) (v : FixedHeavyParameters c) :
    fixedHeavyWord c (fixedHeavyTranslate c A v)=fixedHeavyWord c v ∘ coordinateTranslation A :=
  binaryNormalMap_translation A (v.2.val,v.1.val,c.val)

theorem fixedHeavyWord_injective (c : Point) : Function.Injective (fixedHeavyWord c) := by
  rintro ⟨⟨M,hM⟩,⟨ε,hε⟩⟩ ⟨⟨N,hN⟩,⟨δ,hδ⟩⟩ h
  have he := binaryNormalMap_injective h
  have hε := congrArg Prod.fst he
  have hM := congrArg (fun a : BinaryParameters => a.2.1) he
  dsimp at hε hM
  cases hM
  cases hε
  rfl

theorem fixedHeavyTranslate_involutive (c : Point) (A : BinaryMatrix) :
    Function.Involutive (fixedHeavyTranslate c A) := by
  intro v
  apply fixedHeavyWord_injective c
  rw [fixedHeavyTranslate_word,fixedHeavyTranslate_word]
  funext z
  change fixedHeavyWord c v (z.1,(z.2+matrixAt A z.1.val)+matrixAt A z.1.val)=_
  rw [add_assoc,vector_add_self,add_zero]

noncomputable def fixedHeavyTranslation (c : Point) (A : BinaryMatrix) :
    FixedHeavyParameters c ≃ FixedHeavyParameters c :=
  {toFun := fixedHeavyTranslate c A
   invFun := fixedHeavyTranslate c A
   left_inv := fixedHeavyTranslate_involutive c A
   right_inv := fixedHeavyTranslate_involutive c A}

noncomputable def rowTranslationMatrix (p : Point) (x : E) : BinaryMatrix :=
  outerMatrix x (basisPoint (point_has_one p).choose).val

theorem rowTranslationMatrix_at (p : Point) (x : E) : matrixAt (rowTranslationMatrix p x) p.val=x := by
  rw [rowTranslationMatrix,matrixAt_outer,dot_basisPoint,(point_has_one p).choose_spec,one_smul]

abbrev HeavyAvoidingPair (c p : Point) (x : E) :=
  {v : FixedHeavyParameters c // fixedHeavyWord c v (p,x)=0 ∧ fixedHeavyWord c v (p,x+p.val)=0}

theorem fixedHeavyTranslate_row (c p : Point) (x y : E) (v : FixedHeavyParameters c) :
    fixedHeavyWord c (fixedHeavyTranslate c (rowTranslationMatrix p x) v) (p,y)=
      fixedHeavyWord c v (p,y+x) := by
  rw [fixedHeavyTranslate_word]
  change fixedHeavyWord c v (p,y+matrixAt (rowTranslationMatrix p x) p.val)=_
  rw [rowTranslationMatrix_at]

noncomputable def heavyAvoidingPairEquiv (c p : Point) (x : E) :
    HeavyAvoidingPair c p 0 ≃ HeavyAvoidingPair c p x where
  toFun v := ⟨fixedHeavyTranslate c (rowTranslationMatrix p x) v.val,by
    constructor
    · rw [fixedHeavyTranslate_row,vector_add_self]
      exact v.prop.1
    · rw [fixedHeavyTranslate_row,add_right_comm,vector_add_self]
      exact v.prop.2⟩
  invFun v := ⟨fixedHeavyTranslate c (rowTranslationMatrix p x) v.val,by
    constructor
    · rw [fixedHeavyTranslate_row,zero_add]
      exact v.prop.1
    · rw [fixedHeavyTranslate_row]
      simpa only [zero_add,add_zero,add_comm] using v.prop.2⟩
  left_inv v := Subtype.ext (fixedHeavyTranslate_involutive c (rowTranslationMatrix p x) v.val)
  right_inv v := Subtype.ext (fixedHeavyTranslate_involutive c (rowTranslationMatrix p x) v.val)

end Atlas.Rudvalis
