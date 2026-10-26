import Atlas.Rudvalis.FourSupportTranslations
import Atlas.Rudvalis.BlockLinearGenerators
import Atlas.Rudvalis.MinimumLiftFibres

/-! All admissible four-plane supports belong to one actual binary coordinate orbit. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
theorem binaryPLinear_dual_cycle (a : Point) :
    ∃ r : Fin 7,∀ x : E,dot (binaryLabel 1) ((binaryPLinear^r.val) x)=dot a.val x := by
  decide +kernel +revert

theorem binaryMatrix_pair_basis (M : BinaryMatrix) (i j : Fin 3) :
    dot (matrixAt M (basisPoint i).val) (basisPoint j).val=M j i := by
  rw [dot_comm,dot_basisPoint]
  fin_cases i <;> simp [matrixAt,basisPoint,binaryLabel,Fin.sum_univ_succ]

theorem pullback_outer_of_dual (A : E ≃ₗ[Bit] E) (a b : E)
    (h : ∀ x,dot b (A x)=dot a x) :
    pullbackBinaryMatrix A (outerMatrix b b)=outerMatrix a a := by
  ext j i
  have hp := pullbackBinaryMatrix_pair A (outerMatrix b b) (basisPoint i).val (basisPoint j).val
  rw [binaryMatrix_pair_basis,matrixAt_outer,dot_smul_left,h,h] at hp
  rw [dot_comm a _,dot_basisPoint,dot_comm a _,dot_basisPoint] at hp
  exact hp.trans (mul_comm _ _)

set_option maxHeartbeats 2000000 in
theorem fourSupport_from_base_orbit (ε₀ : Point → Bit)
    (w₀ : minimumLift (binaryNormalMap (ε₀,outerMatrix (binaryLabel 1) (binaryLabel 1),0)))
    (d : BinaryWord) (hd : admissibleFourSupport d) :
    ∃ g : binaryPermutationGroup,d=
      binaryNormalMap (ε₀,outerMatrix (binaryLabel 1) (binaryLabel 1),0) ∘ g.val := by
  obtain ⟨a,ε,rfl,hε,hs⟩ := hd
  obtain ⟨r,hr⟩ := binaryPLinear_dual_cycle a
  let A := binaryPLinear^r.val
  choose t ht using section_difference_origin A
  let g := binarySectionGroupLift A t ht
  let b := sectionPullbackParameters A t (ε₀,outerMatrix (binaryLabel 1) (binaryLabel 1),0)
  have hbM : b.2.1=outerMatrix a.val a.val := pullback_outer_of_dual A a.val (binaryLabel 1) hr
  have hbc : b.2.2=0 := A.symm.map_zero
  have hb : binaryNormalMap (b.1,outerMatrix a.val a.val,0)=
      binaryNormalMap (ε₀,outerMatrix (binaryLabel 1) (binaryLabel 1),0) ∘ g.val := by
    have h := binaryNormalMap_sectionPullback A t ht (ε₀,outerMatrix (binaryLabel 1) (binaryLabel 1),0)
    change binaryNormalMap b=_ at h
    have he : b=(b.1,outerMatrix a.val a.val,0) := Prod.ext rfl (Prod.ext hbM hbc)
    rw [he] at h
    exact h

  have hw₀ : hammingNorm (binaryNormalMap (ε₀,outerMatrix (binaryLabel 1) (binaryLabel 1),0))=16 := by
    rw [← w₀.prop.2]
    exact quaternary_minimum_residue_weight _ w₀.val.prop w₀.prop.1
  have hwb : hammingNorm (binaryNormalMap (b.1,outerMatrix a.val a.val,0))=16 := by
    rw [hb,binaryWord_weight_permute,hw₀]
  have hbsigned := signedLift_nonempty_of_binary_transport g⁻¹ _
    ((minimumSignedLiftEquiv _ hw₀) w₀)
  change Nonempty (SignedLift quaternaryCode
    (binaryNormalMap (ε₀,outerMatrix (binaryLabel 1) (binaryLabel 1),0) ∘ g.val)) at hbsigned
  rw [← hb] at hbsigned
  obtain ⟨wb⟩ := hbsigned
  let wm := (minimumSignedLiftEquiv _ hwb).symm wb
  have hbs := (quaternary_four_active_support_constraint wm.val.val wm.val.prop wm.prop.1
    b.1 a a wm.prop.2).2
  have hbzero (p : Point) (hp : dot a.val p.val=0) : b.1 p=0 :=
    ((binaryNormalMap_bilinear_weight_sixteen b.1 _ (outerMatrix_nonzero _ _ a.prop a.prop)).mp hwb).2
      p (by rw [matrixAt_outer,hp,zero_smul])
  obtain ⟨B,hB⟩ := four_support_fixed_form_translation a b.1 ε hbzero hε (hbs.trans hs.symm)
  refine ⟨g*⟨coordinateTranslation B,coordinateTranslation_mem B⟩,?_⟩
  rw [hB,hb]
  rfl

end Atlas.Rudvalis
