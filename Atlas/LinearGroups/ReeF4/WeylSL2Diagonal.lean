import Atlas.LinearGroups.ReeF4.WeylSL2Representation
import Atlas.LinearGroups.ReeF4.WeylSL2Torus

/-! The actual SL₂ diagonal agrees with the calibrated source torus. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [CharP F 2]

def longSL2DiagonalMatrix (a : Fˣ) : LongSL2 (F := F) :=
  Matrix.SpecialLinearGroup.diag2 (a : F) (Units.ne_zero a)

theorem longSL2DiagonalMatrix_map (σ : F →+* F) (a : Fˣ) :
    Matrix.SpecialLinearGroup.map σ (longSL2DiagonalMatrix a) =
      longSL2DiagonalMatrix (Units.map σ.toMonoidHom a) := by
  apply Subtype.ext
  ext i j
  change σ ((longSL2DiagonalMatrix a : Matrix (Fin 2) (Fin 2) F) i j) =
    (longSL2DiagonalMatrix (Units.map σ.toMonoidHom a) : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;>
    simp [longSL2DiagonalMatrix, Matrix.SpecialLinearGroup.map,
      Matrix.SpecialLinearGroup.diag2_coe']

theorem longSL2DiagonalMatrix_apply (a : Fˣ) (v : Fin 2 → F) :
    Matrix.SpecialLinearGroup.toLin' (longSL2DiagonalMatrix a) v =
      ![(a:F)*v 0, ((a⁻¹:Fˣ):F)*v 1] := by
  funext i
  fin_cases i <;>
    simp [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      longSL2DiagonalMatrix, Matrix.SpecialLinearGroup.diag2_coe',
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem longSL2DiagonalMatrix_tensor (a b : Fˣ) (v : Fin 2 → Fin 2 → F) :
    longSL2TensorCurried (longSL2DiagonalMatrix a) (longSL2DiagonalMatrix b) v =
      ![![(a:F)*(b:F)*v 0 0, (a:F)*((b⁻¹:Fˣ):F)*v 0 1],
        ![((a⁻¹:Fˣ):F)*(b:F)*v 1 0, ((a⁻¹:Fˣ):F)*((b⁻¹:Fˣ):F)*v 1 1]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [longSL2TensorCurried, longSL2Curry, longSL2TensorEquiv,
      longSL2TensorMatrix, Matrix.toLin'_apply,
      longSL2DiagonalMatrix, Matrix.SpecialLinearGroup.diag2_coe',
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two]

set_option maxHeartbeats 800000 in
theorem longSL2Representation_diagonal (σ : F →+* F) (a : Fˣ) :
    longSL2Representation σ (longSL2DiagonalMatrix a) =
      longSL2Diagonal a (Units.map σ.toMonoidHom a) := by
  apply LinearEquiv.ext
  intro w
  apply (longSL2BlocksEquiv (F := F)).injective
  change longSL2BlocksEquiv (longSL2BlocksEquiv.symm
      (longSL2BlocksAction σ (longSL2DiagonalMatrix a) (longSL2ToBlocks w))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i j
    change Matrix.SpecialLinearGroup.toLin' (longSL2DiagonalMatrix a)
      ((longSL2ToBlocks w).1 i) j = _
    rw [longSL2DiagonalMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [longSL2BlocksEquiv, longSL2ToBlocks, longSL2Diagonal,
        longSL2DiagonalWeights, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula]
  · apply Prod.ext
    · funext i j
      change Matrix.SpecialLinearGroup.toLin'
        (Matrix.SpecialLinearGroup.map σ (longSL2DiagonalMatrix a))
        ((longSL2ToBlocks w).2.1 i) j = _
      rw [longSL2DiagonalMatrix_map, longSL2DiagonalMatrix_apply]
      fin_cases i <;> fin_cases j <;>
        simp [longSL2BlocksEquiv, longSL2ToBlocks, longSL2Diagonal,
          longSL2DiagonalWeights, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula]
    · apply Prod.ext
      · funext i j k
        change longSL2TensorCurried (longSL2DiagonalMatrix a)
          (Matrix.SpecialLinearGroup.map σ (longSL2DiagonalMatrix a))
          ((longSL2ToBlocks w).2.2.1 i) j k = _
        rw [longSL2DiagonalMatrix_map, longSL2DiagonalMatrix_tensor]
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          simp [longSL2BlocksEquiv, longSL2ToBlocks, longSL2Diagonal,
            longSL2DiagonalWeights, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula]
      · apply Prod.ext
        · funext i j
          change longSL2TensorCurried (longSL2DiagonalMatrix a) (longSL2DiagonalMatrix a)
            (longSL2ToBlocks w).2.2.2.1 i j = _
          rw [longSL2DiagonalMatrix_tensor]
          fin_cases i <;> fin_cases j <;>
            simp [longSL2BlocksEquiv, longSL2ToBlocks, longSL2Diagonal,
              longSL2DiagonalWeights, rootDiagonalEquiv, rootDiagonalLinear,
              rootDiagonalFormula, pow_two]
        · funext i
          change (longSL2ToBlocks w).2.2.2.2 i = _
          fin_cases i <;>
            simp [longSL2BlocksEquiv, longSL2ToBlocks, longSL2Diagonal,
              longSL2DiagonalWeights, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula]

variable [Finite F]

theorem longSL2Representation_torus (m : ℕ) (a : Fˣ) :
    longSL2Representation (theta F m).toRingHom (longSL2DiagonalMatrix a) =
      torusEquiv m a a⁻¹ := by
  rw [longSL2Representation_diagonal, torusEquiv_longSL2]
  rfl

end Atlas.ReeF4
