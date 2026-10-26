import Atlas.LinearGroups.ReeF4.WeylSL2Generators
import Atlas.LinearGroups.ReeF4.Weyl

/-! The source reflection is the actual Weyl matrix in the retained SL₂ representation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
open scoped Matrix
variable {F : Type*} [Field F] [CharP F 2]

def longSL2Weyl : LongSL2 (F := F) :=
  ⟨!![0,1;1,0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem longSL2Weyl_map (σ : F →+* F) :
    Matrix.SpecialLinearGroup.map σ longSL2Weyl = longSL2Weyl := by
  apply Subtype.ext
  ext i j
  change σ ((longSL2Weyl (F := F) : Matrix (Fin 2) (Fin 2) F) i j) =
    (longSL2Weyl (F := F) : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;> simp [longSL2Weyl]

theorem longSL2Weyl_apply (v : Fin 2 → F) :
    Matrix.SpecialLinearGroup.toLin' longSL2Weyl v = fun i => v (Fin.rev i) := by
  funext i
  change ((longSL2Weyl (F := F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) i = v (Fin.rev i)
  fin_cases i <;>
    simp [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      longSL2Weyl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.rev]

theorem longSL2Weyl_tensor (v : Fin 2 → Fin 2 → F) :
    longSL2TensorCurried longSL2Weyl longSL2Weyl v =
      fun i j => v (Fin.rev i) (Fin.rev j) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [longSL2TensorCurried, longSL2Curry, longSL2TensorEquiv,
      longSL2TensorMatrix, Matrix.toLin'_apply, longSL2Weyl,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.rev]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem longSL2Representation_weyl (σ : F →+* F) :
    longSL2Representation σ longSL2Weyl = weylSigma := by
  apply LinearEquiv.ext
  intro w
  apply (longSL2BlocksEquiv (F := F)).injective
  change longSL2BlocksEquiv (longSL2BlocksEquiv.symm
      (longSL2BlocksAction σ longSL2Weyl (longSL2ToBlocks w))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i j
    change Matrix.SpecialLinearGroup.toLin' longSL2Weyl
      ((longSL2ToBlocks w).1 i) j = _
    rw [longSL2Weyl_apply]
    fin_cases i <;> fin_cases j <;> rfl
  · apply Prod.ext
    · funext i j
      change Matrix.SpecialLinearGroup.toLin'
        (Matrix.SpecialLinearGroup.map σ longSL2Weyl)
        ((longSL2ToBlocks w).2.1 i) j = _
      rw [longSL2Weyl_map, longSL2Weyl_apply]
      fin_cases i <;> fin_cases j <;> rfl
    · apply Prod.ext
      · funext i j k
        change longSL2TensorCurried longSL2Weyl
          (Matrix.SpecialLinearGroup.map σ longSL2Weyl)
          ((longSL2ToBlocks w).2.2.1 i) j k = _
        rw [longSL2Weyl_map, longSL2Weyl_tensor]
        fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl
      · apply Prod.ext
        · funext i j
          change longSL2TensorCurried longSL2Weyl longSL2Weyl
            (longSL2ToBlocks w).2.2.2.1 i j = _
          rw [longSL2Weyl_tensor]
          fin_cases i <;> fin_cases j <;> rfl
        · funext i
          fin_cases i <;> rfl

theorem longSL2_lower (u : F) :
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) u =
      longSL2Weyl * longSL2Upper u * longSL2Weyl := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longSL2Weyl, longSL2Upper, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.single, Matrix.one_apply]

end Atlas.ReeF4
