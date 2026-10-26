import Atlas.Rudvalis.BinaryTranslations
import Atlas.Rudvalis.QuadraticMinimumCount

/-! The cross-product image controlling translations of a heavy quadratic support. -/
namespace Atlas.Rudvalis
open scoped BigOperators

theorem crossMatrix_section_vector (c b : E) (i : Fin 3)
    (hi : c i=1) (hb : dot b c=0) :
    matrixAt (crossMatrix c) (matrixAt (crossMatrix (Pi.single i 1)) b)=b := by
  decide +kernel +revert

theorem crossMatrix_column_dot (c : E) (M : BinaryMatrix)
    (hm : matrixAt M.transpose c=0) (j : Fin 3) : dot (fun i => M i j) c=0 := by
  exact congrFun hm j

theorem crossMatrix_matrix_section (c : E) (M : BinaryMatrix) (i : Fin 3)
    (hi : c i=1) (hm : matrixAt M.transpose c=0) :
    crossMatrix c * (crossMatrix (Pi.single i 1) * M)=M := by
  ext k j
  have h := crossMatrix_section_vector c (fun r => M r j) i hi (crossMatrix_column_dot c M hm j)
  exact congrFun h k

theorem crossMatrix_image (c : E) (hc : c≠0) (M : BinaryMatrix)
    (hm : matrixAt M.transpose c=0) : ∃ A : BinaryMatrix,crossMatrix c*A=M := by
  obtain ⟨i,hi⟩ := point_has_one (⟨c,hc⟩ : Point)
  exact ⟨crossMatrix (Pi.single i 1)*M,crossMatrix_matrix_section c M i hi hm⟩

theorem crossMatrix_outer_zero (c u : E) : crossMatrix c*outerMatrix c u=0 := by
  ext i j
  change (∑ k,crossMatrix c i k*(c k*u j))=0
  have h : (∑ k,crossMatrix c i k*(c k*u j))=(∑ k,crossMatrix c i k*c k)*u j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h]
  have hz : matrixAt (crossMatrix c) c=0 := by decide +kernel +revert
  have hh := congrFun hz i
  change (∑ k,crossMatrix c i k*c k)=0 at hh
  rw [hh,zero_mul]

theorem translatedParameters_heavy_constant (ε : Point→Bit) (M : BinaryMatrix) (c u : E)
    (hm : matrixAt M.transpose c=0) (p : Point) :
    (translatedParameters (outerMatrix c u) (ε,M,c)).1 p=
      ε p + (if p.val=c then dot u c else 0) := by
  change ε p+dot (matrixAt M p.val) (matrixAt (outerMatrix c u) p.val)+
    theta p c (matrixAt (outerMatrix c u) p.val)=_
  rw [matrixAt_outer]
  have hd : dot (matrixAt M p.val) c=0 := by rw [matrixAt_transpose_pair,hm]; simp [dot]
  have h : ∀ a : Bit,a=0 ∨ a=1 := by decide +kernel
  rcases h (dot u p.val) with hz|ho
  · rw [hz,zero_smul,theta_zero]
    simp only [dot,mul_zero,Finset.sum_const_zero,add_zero]
    split_ifs with he
    · simpa [←he,hz]
    · rfl
  · rw [ho,one_smul,hd,add_zero,theta_normalization]
    split_ifs with he
    · rw [←he,ho]
    · rfl

end Atlas.Rudvalis
