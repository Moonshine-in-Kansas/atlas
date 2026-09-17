import Atlas.LinearGroups.Orthogonal.D2MatrixKernel
import Atlas.LinearGroups.Orthogonal.Elementary
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Atlas.LinearGroups.Elementary

/-! # The determinant left-right action lands in the actual elementary group

Source SL2 generation is used directly, including the fields with two and three
elements. No source-group perfectness is assumed.
-/
noncomputable section
namespace Atlas.Orthogonal.D2Matrix
open Matrix Atlas.Quadratic
variable {F : Type*} [Field F]

private theorem coordinate_polar_ee (a : F) :
    (formD 2 F).polarBilin (e 0) (a • e 1) = 0 := by
  rw [map_smul,polarD_e]; simp [e,Pi.single_apply]

private theorem coordinate_polar_ff (a : F) :
    (formD 2 F).polarBilin (f 0) (a • f 1) = 0 := by
  rw [map_smul,polarD_f]; simp [f,Pi.single_apply]

private theorem coordinate_polar_ef (i j : Fin 2) (hij : i ≠ j) (a : F) :
    (formD 2 F).polarBilin (e i) (a • f j) = 0 := by
  rw [map_smul,polarD_f]
  simp [e,Pi.single_apply,hij]

theorem left_upper_root (a : F) :
    toOrthogonal (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a,1) =
      siegelElement (formD 2 F) (e 0) (-a • e 1) (formD_e 0) (coordinate_polar_ee (-a)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change _ = siegel (formD 2 F) (e 0) (-a • e 1) x _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Matrix.adjugate_fin_two, formD_apply, e, f, Fin.sum_univ_two,
      toOrthogonal, onD, coordinates, matrixAction, SpecialLinearGroup.transvection_inv,
      SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.mul_apply,
      Matrix.vecHead, Matrix.vecTail]
    <;> ring

theorem left_lower_root (a : F) :
    toOrthogonal (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a,1) =
      siegelElement (formD 2 F) (f 0) (a • f 1) (formD_f 0) (coordinate_polar_ff a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change _ = siegel (formD 2 F) (f 0) (a • f 1) x _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Matrix.adjugate_fin_two, formD_apply, e, f, Fin.sum_univ_two,
      toOrthogonal, onD, coordinates, matrixAction, SpecialLinearGroup.transvection_inv,
      SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.mul_apply,
      Matrix.vecHead, Matrix.vecTail]
    <;> ring

theorem right_upper_root (a : F) :
    toOrthogonal (1,SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a) =
      siegelElement (formD 2 F) (e 1) (-a • f 0) (formD_e 1)
        (coordinate_polar_ef 1 0 (by decide) (-a)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change _ = siegel (formD 2 F) (e 1) (-a • f 0) x _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Matrix.adjugate_fin_two, formD_apply, e, f, Fin.sum_univ_two,
      toOrthogonal, onD, coordinates, matrixAction, SpecialLinearGroup.transvection_inv,
      SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.mul_apply,
      Matrix.vecHead, Matrix.vecTail]
    <;> ring

theorem right_lower_root (a : F) :
    toOrthogonal (1,SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a) =
      siegelElement (formD 2 F) (e 0) (-a • f 1) (formD_e 0)
        (coordinate_polar_ef 0 1 (by decide) (-a)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change _ = siegel (formD 2 F) (e 0) (-a • f 1) x _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Matrix.adjugate_fin_two, formD_apply, e, f, Fin.sum_univ_two,
      toOrthogonal, onD, coordinates, matrixAction, SpecialLinearGroup.transvection_inv,
      SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.mul_apply,
      Matrix.vecHead, Matrix.vecTail]
    <;> ring

theorem left_mem_elementary (A : SpecialLinearGroup (Fin 2) F) :
    toOrthogonal (A,1) ∈ elementarySubgroup (formD 2 F) := by
  apply Atlas.sl_elementary_induction (fun A => toOrthogonal (A,1) ∈ elementarySubgroup (formD 2 F))
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · rw [left_upper_root]
      exact siegelElement_mem _ _ _ _ _
    · rw [left_lower_root]
      exact siegelElement_mem _ _ _ _ _
    · exact False.elim (hij rfl)
  · intro A B hA hB
    have he : ((A*B,1) : PairSL (F := F)) = (A,1)*(B,1) := by simp
    rw [he,map_mul]
    exact Subgroup.mul_mem _ hA hB

theorem right_mem_elementary (B : SpecialLinearGroup (Fin 2) F) :
    toOrthogonal (1,B) ∈ elementarySubgroup (formD 2 F) := by
  apply Atlas.sl_elementary_induction (fun B => toOrthogonal (1,B) ∈ elementarySubgroup (formD 2 F))
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · rw [right_upper_root]
      exact siegelElement_mem _ _ _ _ _
    · rw [right_lower_root]
      exact siegelElement_mem _ _ _ _ _
    · exact False.elim (hij rfl)
  · intro A B hA hB
    have he : ((1,A*B) : PairSL (F := F)) = (1,A)*(1,B) := by simp
    rw [he,map_mul]
    exact Subgroup.mul_mem _ hA hB

/-- The full actual left-right SL2 product image lies in the actual elementary subgroup. -/
theorem toOrthogonal_mem_elementary (g : PairSL (F := F)) :
    toOrthogonal g ∈ elementarySubgroup (formD 2 F) := by
  have he : g = (g.1,1)*(1,g.2) := by simp
  rw [he,map_mul]
  exact Subgroup.mul_mem _ (left_mem_elementary g.1) (right_mem_elementary g.2)

theorem image_le_elementary : (toOrthogonal (F := F)).range ≤ elementarySubgroup (formD 2 F) := by
  rintro _ ⟨g,rfl⟩
  exact toOrthogonal_mem_elementary g
end Atlas.Orthogonal.D2Matrix
