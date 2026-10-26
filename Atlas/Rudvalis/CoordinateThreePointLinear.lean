import Atlas.Rudvalis.CoordinateTwoRowRigidity

namespace Atlas.Rudvalis

noncomputable def threePointLinearEquiv (p q r : Point) (h : (pairBasisMatrix p q r.val).det=1) : E ≃ₗ[Bit] E :=
  LinearEquiv.ofInjectiveEndo (binaryMatrixLinear (pairBasisMatrix p q r.val))
    (by
      have hC : IsUnit (pairBasisMatrix p q r.val) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [h]; exact isUnit_one)
      exact Matrix.mulVec_injective_iff_isUnit.mpr hC)

theorem threePointLinearEquiv_basis (p q r : Point) (h : (pairBasisMatrix p q r.val).det=1) (i : Fin 3) :
    threePointLinearEquiv p q r h (basisPoint i).val=![p.val,q.val,r.val] i := by
  ext j
  change matrixAt (pairBasisMatrix p q r.val) (basisPoint i).val j= _
  fin_cases i <;> simp [matrixAt,pairBasisMatrix,basisPoint,binaryLabel,Fin.sum_univ_succ]

/-- Prescribe independently the values at three linearly independent Fano labels. -/
theorem matrixAt_three_points (p q r : Point) (h : (pairBasisMatrix p q r.val).det=1) (a b c : E) :
    ∃B : BinaryMatrix,matrixAt B p.val=a ∧ matrixAt B q.val=b ∧ matrixAt B r.val=c := by
  let C := threePointLinearEquiv p q r h
  let D : BinaryMatrix := fun i j => ![a i,b i,c i] j
  let L : E→ₗ[Bit] E := (binaryMatrixLinear D).comp C.symm.toLinearMap
  let B : BinaryMatrix := LinearMap.toMatrix' L
  have hb (i : Fin 3) : matrixAt B (![p.val,q.val,r.val] i)=![a,b,c] i := by
    rw [←threePointLinearEquiv_basis p q r h i]
    change (LinearMap.toMatrix' L).mulVec (C (basisPoint i).val)=_
    rw [LinearMap.toMatrix'_mulVec]
    change matrixAt D (C.symm (C (basisPoint i).val))=_
    rw [C.symm_apply_apply]
    ext j
    fin_cases i <;> simp [matrixAt,D,basisPoint,binaryLabel,Fin.sum_univ_succ]
  exact ⟨B,hb 0,hb 1,hb 2⟩

theorem threePoint_spans (p q r : Point) (h : (pairBasisMatrix p q r.val).det=1) (x : E) :
    ∃a : E,x=a 0 • p.val+a 1 • q.val+a 2 • r.val := by
  obtain ⟨a,ha⟩ := (threePointLinearEquiv p q r h).surjective x
  refine ⟨a,?_⟩
  rw [←ha]
  ext i
  change matrixAt (pairBasisMatrix p q r.val) a i=_
  simp [matrixAt,pairBasisMatrix,Fin.sum_univ_succ]
  ring

end Atlas.Rudvalis
