import Atlas.Rudvalis.FrameSignDifferences

namespace Atlas.Rudvalis
open scoped commutatorElement

noncomputable def binaryMatrixConjugate (A : E ≃ₗ[Bit] E) (M : BinaryMatrix) : BinaryMatrix :=
  binaryLinearMatrix A*M*binaryLinearMatrix A.symm

theorem binaryMatrixConjugate_apply (A : E ≃ₗ[Bit] E) (M : BinaryMatrix) (x : E) :
    matrixAt (binaryMatrixConjugate A M) x=A (matrixAt M (A.symm x)) := by
  rw [binaryMatrixConjugate,matrixAt_mul,matrixAt_mul,binaryLinearMatrix_apply,binaryLinearMatrix_apply]

theorem binarySection_translation_conjugate (A : E ≃ₗ[Bit] E) (t : Point→E)
    (ht : ∀p c x,theta (linearPointEquiv A p) (A c) (A x)+theta p c x=polar c (t p) x) (M : BinaryMatrix) :
    binarySectionGroupLift A t ht * coordinateTranslationHom (Multiplicative.ofAdd M) *
      (binarySectionGroupLift A t ht)⁻¹=
      coordinateTranslationHom (Multiplicative.ofAdd (binaryMatrixConjugate A M)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨⟨p,x⟩,rfl⟩ := (binarySectionLift A t).surjective z
  change binarySectionLift A t (coordinateTranslation M
      ((binarySectionLift A t).symm (binarySectionLift A t (p,x))))=
    coordinateTranslation (binaryMatrixConjugate A M) (binarySectionLift A t (p,x))
  rw [Equiv.symm_apply_apply]
  change (linearPointEquiv A p,A (x+matrixAt M p.val+t p))=
    (linearPointEquiv A p,A (x+t p)+matrixAt (binaryMatrixConjugate A M) (A p.val))
  rw [binaryMatrixConjugate_apply,LinearEquiv.symm_apply_apply]
  congr 1
  rw [show x+matrixAt M p.val+t p=(x+t p)+matrixAt M p.val by abel,map_add]

theorem binarySection_translation_commutator (A : E ≃ₗ[Bit] E) (t : Point→E)
    (ht : ∀p c x,theta (linearPointEquiv A p) (A c) (A x)+theta p c x=polar c (t p) x) (M : BinaryMatrix) :
    ⁅binarySectionGroupLift A t ht,coordinateTranslationHom (Multiplicative.ofAdd M)⁆=
      coordinateTranslationHom (Multiplicative.ofAdd (binaryMatrixConjugate A M-M)) := by
  rw [commutatorElement_def,binarySection_translation_conjugate,←map_inv,←map_mul,sub_eq_add_neg]
  rfl

theorem binaryMatrix_eq_of_apply (M N : BinaryMatrix) (h : ∀x : E,matrixAt M x=matrixAt N x) : M=N := by
  ext i j
  have hj := congrArg (fun x : E=>x i) (h (basisPoint j).val)
  fin_cases j <;> simpa [matrixAt,basisPoint,binaryLabel,Fin.sum_univ_succ] using hj

theorem binaryLinearMatrix_elementary (i j : Fin 3) (hij : i≠j) :
    binaryLinearMatrix (binaryElementaryLinear i j hij)=binaryElementaryMatrix i j := by
  apply binaryMatrix_eq_of_apply
  intro x
  rw [binaryLinearMatrix_apply,binaryElementaryLinear_apply]
  rfl

theorem binaryElementaryLinear_symm (i j : Fin 3) (hij : i≠j) :
    (binaryElementaryLinear i j hij).symm=binaryElementaryLinear i j hij := by
  apply LinearEquiv.ext
  intro x
  apply (binaryElementaryLinear i j hij).injective
  rw [LinearEquiv.apply_symm_apply,binaryElementaryLinear_apply,binaryElementaryLinear_apply,
    Matrix.mulVec_mulVec,binaryElementaryMatrix_square i j hij,Matrix.one_mulVec]

theorem binaryMatrixConjugate_elementary (i j : Fin 3) (hij : i≠j) (M : BinaryMatrix) :
    binaryMatrixConjugate (binaryElementaryLinear i j hij) M-M=binaryMatrixDifference i j M := by
  rw [binaryMatrixConjugate,binaryElementaryLinear_symm,binaryLinearMatrix_elementary]
  rfl

end Atlas.Rudvalis
