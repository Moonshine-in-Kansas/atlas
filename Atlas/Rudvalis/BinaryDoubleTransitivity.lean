import Atlas.Rudvalis.BinaryLiftAction

/-! Double transitivity of the actual binary code group on its seven blocks. -/
namespace Atlas.Rudvalis

def pairBasisMatrix (p q : Point) (v : E) : BinaryMatrix :=
  fun i j => ![p.val i,q.val i,v i] j

set_option maxHeartbeats 1000000 in
theorem point_pair_basis_completion (p q : Point) (hpq : p≠q) :
    ∃ v : E, (pairBasisMatrix p q v).det=1 := by
  decide +kernel +revert

theorem point_pair_linearEquiv (p q r s : Point) (hpq : p≠q) (hrs : r≠s) :
    ∃ A : E ≃ₗ[Bit] E, A p.val=r.val ∧ A q.val=s.val := by
  obtain ⟨v,hv⟩ := point_pair_basis_completion p q hpq
  obtain ⟨w,hw⟩ := point_pair_basis_completion r s hrs
  have hC : IsUnit (pairBasisMatrix p q v) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hv]; exact isUnit_one)
  have hD : IsUnit (pairBasisMatrix r s w) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hw]; exact isUnit_one)
  let C : E ≃ₗ[Bit] E := LinearEquiv.ofInjectiveEndo
    (binaryMatrixLinear (pairBasisMatrix p q v)) (Matrix.mulVec_injective_iff_isUnit.mpr hC)
  let D : E ≃ₗ[Bit] E := LinearEquiv.ofInjectiveEndo
    (binaryMatrixLinear (pairBasisMatrix r s w)) (Matrix.mulVec_injective_iff_isUnit.mpr hD)
  have hCp : C (basisPoint 0).val=p.val := by
    ext i
    change matrixAt (pairBasisMatrix p q v) (basisPoint 0).val i=p.val i
    simp [matrixAt,pairBasisMatrix,basisPoint,binaryLabel,Fin.sum_univ_succ]
  have hCq : C (basisPoint 1).val=q.val := by
    ext i
    change matrixAt (pairBasisMatrix p q v) (basisPoint 1).val i=q.val i
    simp [matrixAt,pairBasisMatrix,basisPoint,binaryLabel,Fin.sum_univ_succ]
  have hDr : D (basisPoint 0).val=r.val := by
    ext i
    change matrixAt (pairBasisMatrix r s w) (basisPoint 0).val i=r.val i
    simp [matrixAt,pairBasisMatrix,basisPoint,binaryLabel,Fin.sum_univ_succ]
  have hDs : D (basisPoint 1).val=s.val := by
    ext i
    change matrixAt (pairBasisMatrix r s w) (basisPoint 1).val i=s.val i
    simp [matrixAt,pairBasisMatrix,basisPoint,binaryLabel,Fin.sum_univ_succ]
  refine ⟨C.symm.trans D,?_,?_⟩
  · change D (C.symm p.val)=r.val
    rw [← hCp,C.symm_apply_apply,hDr]
  · change D (C.symm q.val)=s.val
    rw [← hCq,C.symm_apply_apply,hDs]

theorem binaryBlockHom_doubly_transitive (p q r s : Point) (hpq : p≠q) (hrs : r≠s) :
    ∃ g : binaryPermutationGroup, binaryBlockHom g p=r ∧ binaryBlockHom g q=s := by
  obtain ⟨A,hp,hq⟩ := point_pair_linearEquiv p q r s hpq hrs
  obtain ⟨g,hg⟩ := binaryBlockLinearHom_surjective A
  refine ⟨g,?_,?_⟩
  · apply Subtype.ext
    calc
      (binaryBlockHom g p).val=binaryBlockLinearHom g p.val := (binaryBlockLinearEquiv_point g p).symm
      _ = A p.val := by rw [hg]
      _ = r.val := hp
  · apply Subtype.ext
    calc
      (binaryBlockHom g q).val=binaryBlockLinearHom g q.val := (binaryBlockLinearEquiv_point g q).symm
      _ = A q.val := by rw [hg]
      _ = s.val := hq

end Atlas.Rudvalis
