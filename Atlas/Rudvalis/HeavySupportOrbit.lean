import Atlas.Rudvalis.HeavyFixedTranslation
import Atlas.Rudvalis.BlockLinearGenerators
import Atlas.Rudvalis.HeavySeedLifts

/-! All heavy minimum supports lie in the actual binary coordinate orbit of seed B. -/
namespace Atlas.Rudvalis

theorem binaryPLinear_nonzero_cycle (c : E) (hc : c≠0) :
    ∃ r : Fin 7,(binaryPLinear^r.val) c=binaryLabel 6 := by
  decide +kernel +revert

theorem heavySeedResidue_weight : hammingNorm heavySeedResidue=16 := by
  rw [←heavySeedMinimumLift.prop.2]
  exact quaternary_minimum_residue_weight _ heavySeedMinimumLift.val.prop heavySeedMinimumLift.prop.1

theorem heavySupport_seed_orbit (ε : Point→Bit) (M : BinaryMatrix) (c : E)
    (hc : c≠0) (hw : hammingNorm (binaryNormalMap (ε,M,c))=16) :
    ∃ g : binaryPermutationGroup,binaryNormalMap (ε,M,c)=heavySeedResidue ∘ g.val := by
  obtain ⟨r,hr⟩ := binaryPLinear_nonzero_cycle c hc
  let A := binaryPLinear^r.val
  choose t ht using section_difference_origin A
  let g := binarySectionGroupLift A t ht
  let a := sectionPullbackParameters A t seedBParameters
  have ha : a.2.2=c := by
    change A.symm (binaryLabel 6)=c
    exact A.symm_apply_eq.mpr hr.symm
  have hb : binaryNormalMap a=heavySeedResidue ∘ g.val := by
    rw [show heavySeedResidue=binaryNormalMap seedBParameters from seedB_residue]
    exact binaryNormalMap_sectionPullback A t ht seedBParameters
  have hwa : hammingNorm (binaryNormalMap (a.1,a.2.1,c))=16 := by
    rw [←ha]
    change hammingNorm (binaryNormalMap a)=16
    rw [hb,binaryWord_weight_permute,heavySeedResidue_weight]
  obtain ⟨B,hB⟩ := quadratic_minimum_fixed_radical_translation a.1 ε a.2.1 M c hc hwa hw
  refine ⟨g*⟨coordinateTranslation B,coordinateTranslation_mem B⟩,?_⟩
  rw [hB,←ha]
  change (binaryNormalMap a ∘ coordinateTranslation B)=_
  rw [hb]
  rfl

end Atlas.Rudvalis
