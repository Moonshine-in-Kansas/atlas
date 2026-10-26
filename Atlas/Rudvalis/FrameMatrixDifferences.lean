import Atlas.Rudvalis.FramePerfectLinearAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

namespace Atlas.Rudvalis
open scoped BigOperators

def binaryMatrixUnit (i j : Fin 3) : BinaryMatrix := Pi.single i (Pi.single j 1)
def binaryElementaryMatrix (i j : Fin 3) : BinaryMatrix := 1+binaryMatrixUnit i j

def binaryMatrixDifference (i j : Fin 3) (A : BinaryMatrix) : BinaryMatrix :=
  binaryElementaryMatrix i j*A*binaryElementaryMatrix i j-A

theorem binaryElementaryMatrix_square (i j : Fin 3) (hij : i≠j) :
    binaryElementaryMatrix i j*binaryElementaryMatrix i j=1 := by
  decide +kernel +revert

theorem binaryMatrixDifference_offdiagonal (i j : Fin 3) (hij : i≠j) :
    binaryMatrixDifference i j (binaryMatrixUnit j j)=binaryMatrixUnit i j := by
  decide +kernel +revert

theorem binaryMatrixDifference_diagonal (i j : Fin 3) (hij : i≠j) :
    binaryMatrixDifference i j (binaryMatrixUnit j i)=
      binaryMatrixUnit i i+binaryMatrixUnit j j+binaryMatrixUnit i j := by
  decide +kernel +revert

theorem binaryMatrixDifference_trace (i j : Fin 3) (hij : i≠j) (A : BinaryMatrix) :
    Matrix.trace (binaryMatrixDifference i j A)=0 := by
  rw [binaryMatrixDifference,Matrix.trace_sub,Matrix.trace_mul_cycle]
  rw [binaryElementaryMatrix_square i j hij,Matrix.one_mul,sub_self]

/-- Conjugation differences and the scalar identity span every three-by-three binary matrix. -/
theorem binaryMatrix_differences_scalar_span (W : Submodule Bit BinaryMatrix)
    (hI : (1 : BinaryMatrix)∈W)
    (hD : ∀i j : Fin 3,i≠j → ∀A : BinaryMatrix,binaryMatrixDifference i j A∈W) : W=⊤ := by
  have hoff (i j : Fin 3) (hij : i≠j) : binaryMatrixUnit i j∈W := by
    rw [←binaryMatrixDifference_offdiagonal i j hij]
    exact hD i j hij _
  have hdiag (i j : Fin 3) (hij : i≠j) : binaryMatrixUnit i i+binaryMatrixUnit j j∈W := by
    have h := W.add_mem (hD i j hij (binaryMatrixUnit j i)) (hoff i j hij)
    have hz : binaryMatrixUnit i j+binaryMatrixUnit i j=0 := by
      ext r s; exact CharTwo.add_self_eq_zero _
    rw [binaryMatrixDifference_diagonal i j hij,add_assoc,hz,add_zero] at h
    exact h
  have hunit (i j : Fin 3) : binaryMatrixUnit i j∈W := by
    by_cases hij : i=j
    · subst j
      obtain ⟨j,hji⟩ := exists_ne i
      obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
      have he : binaryMatrixUnit i i=1+(binaryMatrixUnit i i+binaryMatrixUnit j j)+
          (binaryMatrixUnit i i+binaryMatrixUnit k k) := by
        have cert : ∀i j k : Fin 3,j≠i → k≠i → k≠j →
          binaryMatrixUnit i i=1+(binaryMatrixUnit i i+binaryMatrixUnit j j)+
            (binaryMatrixUnit i i+binaryMatrixUnit k k) := by decide +kernel
        exact cert i j k hji hki hkj
      rw [he]
      exact W.add_mem (W.add_mem hI (hdiag i j hji.symm)) (hdiag i k hki.symm)
    · exact hoff i j hij
  apply Submodule.eq_top_iff'.mpr
  intro M
  rw [←binaryMatrix_single_expansion M]
  exact W.sum_mem (fun i _=>W.sum_mem (fun j _=>W.smul_mem _ (hunit i j)))

end Atlas.Rudvalis
