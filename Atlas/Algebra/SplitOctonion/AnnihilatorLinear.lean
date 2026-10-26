import Atlas.Algebra.SplitOctonion.AnnihilatorTables

namespace Atlas.SplitOctonion.Annihilator
variable {F : Type*} [Field F]

set_option maxHeartbeats 1600000 in
-- Eight sparse linearity checks, each with eight coordinates.
def leftNumeratorLinear (B : Carrier F) (i : Fin 8) : Parameters F →ₗ[F] Carrier F where
  toFun a := leftNumerator B a i
  map_add' a b := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [leftNumerator,Matrix.vecHead,Matrix.vecTail] <;> ring
  map_smul' s a := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [leftNumerator,Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
-- Eight sparse linearity checks, each with eight coordinates.
def rightNumeratorLinear (B : Carrier F) (i : Fin 8) : Parameters F →ₗ[F] Carrier F where
  toFun c := rightNumerator B c i
  map_add' a b := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [rightNumerator,Matrix.vecHead,Matrix.vecTail] <;> ring
  map_smul' s a := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [rightNumerator,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem leftCorrection_zero (i : Fin 8) : leftCorrection (0 : Carrier F) i=0 := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [leftCorrection]

theorem rightCorrection_zero (i : Fin 8) : rightCorrection (0 : Carrier F) i=0 := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [rightCorrection]

end Atlas.SplitOctonion.Annihilator
