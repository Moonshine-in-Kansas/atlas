import Atlas.LinearGroups.ReeF4.WeylSL2Representation

/-! Matching the abstract SL₂ matrices with actual retained coordinate operators. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [CharP F 2]

def longSL2Upper (u : F) : LongSL2 (F := F) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) u

theorem longSL2Upper_map (σ : F →+* F) (u : F) :
    Matrix.SpecialLinearGroup.map σ (longSL2Upper u) = longSL2Upper (σ u) := by
  apply Subtype.ext
  ext i j
  change σ ((longSL2Upper u : Matrix (Fin 2) (Fin 2) F) i j) =
    (longSL2Upper (σ u) : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;>
    simp [longSL2Upper, Matrix.SpecialLinearGroup.map,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.one_apply]

theorem longSL2Upper_apply (u : F) (v : Fin 2 → F) :
    Matrix.SpecialLinearGroup.toLin' (longSL2Upper u) v = ![v 0 + u*v 1, v 1] := by
  funext i
  fin_cases i <;>
    simp [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      longSL2Upper, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.single, Matrix.one_apply] <;> ring

theorem longSL2Upper_tensor (u z : F) (v : Fin 2 → Fin 2 → F) :
    longSL2TensorCurried (longSL2Upper u) (longSL2Upper z) v =
      ![![v 0 0 + z*v 0 1 + u*v 1 0 + u*z*v 1 1, v 0 1 + u*v 1 1],
        ![v 1 0 + z*v 1 1, v 1 1]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [longSL2TensorCurried, longSL2Curry, longSL2TensorEquiv,
      longSL2TensorMatrix, Matrix.toLin'_apply,
      longSL2Upper, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single, Matrix.one_apply] <;> ring

set_option maxHeartbeats 800000 in
theorem longSL2Representation_upper (σ : F →+* F) (u : F) :
    longSL2Representation σ (longSL2Upper u) = longSL2Equiv u (σ u) := by
  apply LinearEquiv.ext
  intro w
  apply (longSL2BlocksEquiv (F := F)).injective
  change longSL2BlocksEquiv (longSL2BlocksEquiv.symm
      (longSL2BlocksAction σ (longSL2Upper u) (longSL2ToBlocks w))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i j
    change Matrix.SpecialLinearGroup.toLin' (longSL2Upper u)
      ((longSL2ToBlocks w).1 i) j = _
    rw [longSL2Upper_apply]
    fin_cases i <;> fin_cases j <;>
      simp [longSL2ToBlocks, longSL2BlocksEquiv, longSL2Equiv,
        longSL2Linear, longSL2Formula] <;> ring
  · apply Prod.ext
    · funext i j
      change Matrix.SpecialLinearGroup.toLin'
        (Matrix.SpecialLinearGroup.map σ (longSL2Upper u))
        ((longSL2ToBlocks w).2.1 i) j = _
      rw [longSL2Upper_map, longSL2Upper_apply]
      fin_cases i <;> fin_cases j <;>
        simp [longSL2ToBlocks, longSL2BlocksEquiv, longSL2Equiv,
          longSL2Linear, longSL2Formula] <;> ring
    · apply Prod.ext
      · funext i j k
        change longSL2TensorCurried (longSL2Upper u)
          (Matrix.SpecialLinearGroup.map σ (longSL2Upper u))
          ((longSL2ToBlocks w).2.2.1 i) j k = _
        rw [longSL2Upper_map, longSL2Upper_tensor]
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          simp [longSL2ToBlocks, longSL2BlocksEquiv, longSL2Equiv,
            longSL2Linear, longSL2Formula] <;> ring
      · apply Prod.ext
        · funext i j
          change longSL2TensorCurried (longSL2Upper u) (longSL2Upper u)
            (longSL2ToBlocks w).2.2.2.1 i j = _
          rw [longSL2Upper_tensor]
          fin_cases i <;> fin_cases j <;>
            simp [longSL2ToBlocks, longSL2BlocksEquiv, longSL2Equiv,
              longSL2Linear, longSL2Formula] <;> ring
        · funext i
          fin_cases i <;> rfl

end Atlas.ReeF4
