import Atlas.Rudvalis.BlockParityFunctional
import Atlas.Rudvalis.QuaternaryMinimumShape

/-! Inactive-row first moments constrain the rank-one minimum supports. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

theorem blockLiftHalf_coordinates (r s : Fin 7) (k : Fin 8) :
    blockLiftHalf r (seedCoordinateEquiv (s,k))=
      if blockLiftTable (seedShiftedRow r s) k=2 then 1 else 0 := by
  unfold blockLiftHalf
  rw [quaternaryBlockLift_coordinates]

theorem blockLiftHalf_row_sum (r : Fin 7) (p : Point) :
    (∑ x : E,blockLiftHalf r (p,x))=if p=rowLabel r then 0 else 1 := by
  obtain ⟨s,rfl⟩ := rowLabel_bijective.2 p
  rw [← Equiv.sum_comp (seedInnerEquiv s)]
  change (∑ k : Fin 8,blockLiftHalf r (seedCoordinateEquiv (s,k)))=_
  simp_rw [blockLiftHalf_coordinates]
  decide +kernel +revert

noncomputable def blockFirstMoment (r : Fin 7) (p : Point) : E :=
  ∑ x : E,blockLiftHalf r (p,x) • x

noncomputable def blockSupportMoment (r : Fin 7) (a : E) : E :=
  ∑ p : Point,dot a p.val • blockFirstMoment r p

theorem dot_sum_right {ι : Type*} [Fintype ι] (b : E) (v : ι → E) :
    dot b (∑ i,v i)=∑ i,dot b (v i) := by
  simp only [dot,Finset.sum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem dot_smul_right (b v : E) (a : Bit) : dot b (a • v)=a*dot b v := by
  rw [dot_comm,dot_smul_left,dot_comm]

set_option maxHeartbeats 2000000 in
theorem blockParityFunctional_bilinear (r : Fin 7) (ε : Point → Bit) (a b : E) :
    blockParityFunctional r (binaryNormalMap (ε,outerMatrix b a,0)) =
      (∑ p : Point,if p=rowLabel r then 0 else ε p)+dot b (blockSupportMoment r a) := by
  change (∑ z : Coordinate,blockLiftHalf r z * binaryNormalMap (ε,outerMatrix b a,0) z)=_
  rw [Fintype.sum_prod_type]
  have hw (p : Point) (x : E) : binaryNormalMap (ε,outerMatrix b a,0) (p,x)=
      ε p+dot a p.val*dot b x := by
    change ε p+dot (matrixAt (outerMatrix b a) p.val) x+theta p 0 x=_
    rw [matrixAt_outer,dot_smul_left,theta_zero_parameter,add_zero]
  simp_rw [hw,mul_add,Finset.sum_add_distrib]
  apply congrArg₂ (fun x y : Bit => x+y)
  · apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_mul,blockLiftHalf_row_sum]
    split_ifs <;> simp
  · rw [blockSupportMoment,dot_sum_right]
    apply Finset.sum_congr rfl
    intro p _
    rw [dot_smul_right,blockFirstMoment,dot_sum_right]
    simp_rw [dot_smul_right]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring


theorem blockFirstMoment_coordinates (r s : Fin 7) : blockFirstMoment r (rowLabel s)=
    ∑ k : Fin 8,(if blockLiftTable (seedShiftedRow r s) k=2 then (1 : Bit) else 0) • seedInnerLabel s k := by
  unfold blockFirstMoment
  rw [← Equiv.sum_comp (seedInnerEquiv s)]
  apply Finset.sum_congr rfl
  intro k _
  change blockLiftHalf r (seedCoordinateEquiv (s,k)) • seedInnerLabel s k=_
  rw [blockLiftHalf_coordinates]

def blockSupportMomentTable (r : Fin 7) (a : Fin 8) : E := binaryLabel
  (![![0,1,0,1,5,4,5,4],![0,5,7,2,5,0,2,7],![0,3,3,0,7,4,4,7],
    ![0,0,2,2,6,6,4,4],![0,3,2,1,0,3,2,1],![0,5,3,6,6,3,5,0],
    ![0,1,7,6,7,6,0,1]] r a)

set_option maxHeartbeats 2000000 in
theorem blockSupportMoment_table (r : Fin 7) (a : Fin 8) :
    blockSupportMoment r (binaryLabel a)=blockSupportMomentTable r a := by
  unfold blockSupportMoment
  rw [← Equiv.sum_comp rowEquiv]
  change (∑ s : Fin 7,dot (binaryLabel a) (rowLabel s).val • blockFirstMoment r (rowLabel s))=_
  simp_rw [blockFirstMoment_coordinates]
  ext j
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  fin_cases j <;> decide +kernel +revert

theorem blockSupportMoment_obstruction (a b : Point) (e : Bit)
    (h : ∀ r : Fin 7,dot a.val (rowLabel r).val=0 → e+dot b.val (blockSupportMoment r a.val)=0) :
    b=a ∧ e=1 := by
  have he : ∀ i j : Fin 8,∀ e : Bit,binaryLabel i≠0 → binaryLabel j≠0 →
      (∀ r : Fin 7,dot (binaryLabel i) (rowLabel r).val=0 →
        e+dot (binaryLabel j) (blockSupportMomentTable r i)=0) →
      binaryLabel j=binaryLabel i ∧ e=1 := by
    let : DecidableEq E := Fintype.decidablePiFintype
    decide
  obtain ⟨i,hi⟩ := binaryLabel_bijective.2 a.val
  obtain ⟨j,hj⟩ := binaryLabel_bijective.2 b.val
  have ha : binaryLabel i≠0 := hi ▸ a.prop
  have hb : binaryLabel j≠0 := hj ▸ b.prop
  have hcond (r : Fin 7) (hr : dot (binaryLabel i) (rowLabel r).val=0) :
      e+dot (binaryLabel j) (blockSupportMomentTable r i)=0 := by
    rw [← blockSupportMoment_table,hi,hj]
    exact h r (hi ▸ hr)
  obtain ⟨hab,he⟩ := he i j e ha hb hcond
  exact ⟨Subtype.ext (hj.symm.trans (hab.trans hi)),he⟩

theorem quaternary_four_active_support_constraint (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) (ε : Point → Bit) (a b : Point)
    (hr : reduce w=binaryNormalMap (ε,outerMatrix b.val a.val,0)) :
    b=a ∧ (∑ p : Point,ε p)=1 := by
  have hnorm : hammingNorm (binaryNormalMap (ε,outerMatrix b.val a.val,0))=16 := by
    rw [← hr]
    exact quaternary_minimum_residue_weight w hw hweight
  have hM := outerMatrix_nonzero b.val a.val b.prop a.prop
  have hε := ((binaryNormalMap_bilinear_weight_sixteen ε _ hM).mp hnorm).2
  have hn := quaternary_minimum_no_twos w hw hweight
  apply blockSupportMoment_obstruction a b
  intro r hrzero
  have heps : ε (rowLabel r)=0 := hε _ (by rw [matrixAt_outer,hrzero,zero_smul])
  have hzero (x : E) : reduce w (rowLabel r,x)=0 := by
    rw [hr]
    change ε (rowLabel r)+dot (matrixAt (outerMatrix b.val a.val) (rowLabel r).val) x+
      theta (rowLabel r) 0 x=0
    rw [heps,matrixAt_outer,hrzero,zero_smul,theta_zero_parameter]
    simp [dot]
  have hp := blockParityFunctional_inactive r w hw hzero
  have hc : rowTwoCount w (rowLabel r)=0 := by simp [rowTwoCount,hn]
  rw [hc,Nat.cast_zero,hr,blockParityFunctional_bilinear] at hp
  have he : (∑ p : Point,if p=rowLabel r then (0 : Bit) else ε p)=∑ p : Point,ε p := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hpr : p=rowLabel r
    · subst p; simp [heps]
    · simp [hpr]
  rw [he] at hp
  exact hp.symm

end Atlas.Rudvalis

