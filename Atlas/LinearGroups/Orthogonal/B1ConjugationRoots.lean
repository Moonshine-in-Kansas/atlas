import Atlas.LinearGroups.Orthogonal.B1ConjugationAction
import Atlas.LinearGroups.Orthogonal.ElementaryNormal
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Atlas.LinearGroups.Elementary

/-! # Rank-one Siegel roots and the actual SL₂ conjugation generators -/
noncomputable section
namespace Atlas.Orthogonal.B1Conjugation
open Atlas.Quadratic Matrix
variable {F : Type*} [Field F]

set_option maxHeartbeats 1200000 in
theorem standard_siegel_image (v : VectorB 1 F)
    (hv : (formB 1 F).polarBilin (e 0,0) v = 0) :
    siegelElement (formB 1 F) (e 0,0) v (by simp [e]) hv =
      toOrthogonal (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-v.2)) := by
  have hv0 : v.1 (.inr 0) = 0 := by
    have hh := hv
    simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,e,
      Fin.sum_univ_one] at hh
    linear_combination hh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · ext i
    rcases i with i|i <;> fin_cases i
    all_goals
      change (siegel (formB 1 F) (e 0,0) v x).1 _ = _
      simp [siegel,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,e,
        Fin.sum_univ_one,hv0,toOrthogonal,onB,coordinates,kernelAction,kernelMap,
        SpecialLinearGroup.transvection_coe,Matrix.adjugate_fin_two,Matrix.mul_apply,
        Matrix.vecMul,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail]
      <;> ring
  · change (siegel (formB 1 F) (e 0,0) v x).2 = _
    simp [siegel,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,e,
      Fin.sum_univ_one,hv0,toOrthogonal,onB,coordinates,kernelAction,kernelMap,
      SpecialLinearGroup.transvection_coe,Matrix.adjugate_fin_two,Matrix.mul_apply,
      Matrix.vecMul,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail]
    <;> ring

set_option maxHeartbeats 1200000 in
theorem lower_transvection_root (a : F) :
    toOrthogonal (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) a) =
      siegelElement (formB 1 F) (f 0,0) (0,a) (by simp [f]) (by
        simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,f,
          Fin.sum_univ_one] <;> ring) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · ext i
    rcases i with i|i <;> fin_cases i
    all_goals
      change _ = (siegel (formB 1 F) (f 0,0) (0,a) x).1 _
      simp [siegel,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,f,
        Fin.sum_univ_one,toOrthogonal,onB,coordinates,kernelAction,kernelMap,
        SpecialLinearGroup.transvection_coe,Matrix.adjugate_fin_two,Matrix.mul_apply,
        Matrix.vecMul,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail]
      <;> ring
  · change _ = (siegel (formB 1 F) (f 0,0) (0,a) x).2
    simp [siegel,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,f,
      Fin.sum_univ_one,toOrthogonal,onB,coordinates,kernelAction,kernelMap,
      SpecialLinearGroup.transvection_coe,Matrix.adjugate_fin_two,Matrix.mul_apply,
      Matrix.vecMul,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail]
    <;> ring

end Atlas.Orthogonal.B1Conjugation
