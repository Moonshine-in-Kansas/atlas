import Atlas.Rudvalis.HeavyPairSignedOrbit
import Atlas.Rudvalis.BinaryDoubleTransitivity

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- Correct a lifted linear block map at the chosen Gaussian pair. -/
theorem heavy_pair_label_transport (c d p : Point) (hpc : p≠c) (hpd : p≠d)
    (v : HeavyAvoidingPair c p 0) :
    ∃g : codeGroup,∃w : HeavyAvoidingPair d p 0,
      g • coordinateCross (p,0)=coordinateCross (p,0) ∧
      fixedHeavyWord d w.val=fixedHeavyWord c v.val ∘ g.val.right.symm := by
  obtain ⟨A,hAp,hAd⟩ := point_pair_linearEquiv p d p c hpd hpc
  choose t ht using section_difference_origin A
  let B := rowTranslationMatrix p (t p)
  let b : binaryPermutationGroup := binarySectionGroupLift A t ht *
    coordinateTranslationHom (Multiplicative.ofAdd B)
  have hb (y : E) : b.val (p,y)=(p,A y) := by
    change binarySectionLift A t (p,y+matrixAt B p.val)=(p,A y)
    rw [binarySectionLift_apply]
    have hpA : linearPointEquiv A p=p := Subtype.ext hAp
    rw [hpA,rowTranslationMatrix_at,add_assoc,vector_add_self,add_zero]
  let a := translatedParameters B (sectionPullbackParameters A t (v.val.2.val,v.val.1.val,c.val))
  have hac : a.2.2=d.val := by
    change A.symm c.val=d.val
    rw [←hAd,A.symm_apply_apply]
  have ha : a=(a.1,a.2.1,d.val) := Prod.ext rfl (Prod.ext rfl hac)
  have hword : binaryNormalMap (a.1,a.2.1,d.val)=fixedHeavyWord c v.val ∘ b.val := by
    rw [←ha,binaryNormalMap_translation,binaryNormalMap_sectionPullback A t ht]
    rfl
  have hweight : hammingNorm (binaryNormalMap (a.1,a.2.1,d.val))=16 := by
    rw [hword,binaryWord_weight_permute]
    exact v.val.2.prop
  let w' : FixedHeavyParameters d :=
    ⟨⟨a.2.1,binaryNormalMap_quadratic_minimum_contraction (a.1,a.2.1,d.val) d.prop hweight⟩,
      ⟨a.1,hweight⟩⟩
  have hw : fixedHeavyWord d w'=fixedHeavyWord c v.val ∘ b.val := hword
  have havoid : fixedHeavyWord d w' (p,0)=0 ∧ fixedHeavyWord d w' (p,0+p.val)=0 := by
    constructor
    · rw [hw]
      change fixedHeavyWord c v.val (b.val (p,0))=0
      rw [hb,map_zero]
      exact v.prop.1
    · rw [hw]
      change fixedHeavyWord c v.val (b.val (p,0+p.val))=0
      rw [hb,map_add,map_zero,hAp]
      exact v.prop.2
  obtain ⟨g,hg⟩ := codePermutationHom_surjective b⁻¹
  have hgr : g.val.right=b.val.symm := congrArg Subtype.val hg
  have hgs : g.val.right.symm=b.val := by rw [hgr]; rfl
  refine ⟨g,⟨w',havoid⟩,?_,?_⟩
  · rw [coordinateCross_action,hgr]
    have h0 : b.val.symm (p,0)=(p,0) := by
      apply b.val.injective
      rw [Equiv.apply_symm_apply,hb,map_zero]
    rw [h0]
  · rw [hgs]
    exact hw

/-- Actual coordinate-cross stabilizers fuse the six admissible heavy labels. -/
theorem heavy_pair_all_labels_signedLift_transitive (c d p : Point)
    (hpc : p≠c) (hpd : p≠d) (v : HeavyAvoidingPair c p 0) (w : HeavyAvoidingPair d p 0)
    (a : SignedLift quaternaryCode (fixedHeavyWord c v.val))
    (b : SignedLift quaternaryCode (fixedHeavyWord d w.val)) :
    ∃g : codeGroup,g • coordinateCross (p,0)=coordinateCross (p,0) ∧
      monomialHom g.val a.val.val=b.val.val := by
  obtain ⟨g,u,hg,hu⟩ := heavy_pair_label_transport c d p hpc hpd v
  let a' : SignedLift quaternaryCode (fixedHeavyWord d u.val) :=
    ⟨⟨monomialHom g.val a.val.val,(g.prop _).mp a.val.prop⟩,by
      change reduce (monomialAction g.val a.val.val)=fixedHeavyWord d u.val
      rw [monomialAction_reduce,a.prop.1]
      exact hu.symm,monomial_no_twos g.val a.val.val a.prop.2⟩
  obtain ⟨k,hk,hka⟩ := heavy_pair_signedLift_transitive d p hpd u w a' b
  refine ⟨k*g,?_,?_⟩
  · rw [mul_smul,hg,hk]
  · change monomialHom (k.val*g.val) a.val.val=b.val.val
    rw [map_mul]
    exact hka

end Atlas.Rudvalis
