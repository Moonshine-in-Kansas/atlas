import Atlas.LinearGroups.Triality.Torus
import Atlas.LinearGroups.Triality.ShortRankOne
import Atlas.LinearGroups.Triality.LongRankOne

/-! Identify the diagonal torus with the two actual rank-one diagonal images. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Matrix
variable {K : Type*} [Field K]

def diagonalSL (a : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  SpecialLinearGroup.diag2 a a.ne_zero

theorem map_diagonalSL {L : Type*} [Field L] (e : K →+* L) (a : Kˣ) :
    SpecialLinearGroup.map e (diagonalSL a) = diagonalSL (Units.map e.toMonoidHom a) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagonalSL, SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.diag2_coe']

theorem signTwist_diagonalSL (a : Kˣ) : signTwist (diagonalSL a) = diagonalSL a := by
  apply Subtype.ext
  change signMatrix (diagonalSL a).val = (diagonalSL a).val
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [signMatrix, diagonalSL, SpecialLinearGroup.diag2_coe']

theorem contragredient_diagonalSL (a : Kˣ) : contragredient (diagonalSL a) = diagonalSL a⁻¹ := by
  apply Subtype.ext
  change (diagonalSL a)⁻¹.val.transpose = _
  simp only [diagonalSL, SpecialLinearGroup.diag2_inv]
  ext i j; fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.diag2_coe']

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

set_option maxHeartbeats 3000000 in
-- Check the fixed eight coordinate weights of the three twisted rank-one factors.
theorem short_diagonal_torus (a : Kˣ) :
    rankOneShortOrthogonal F K (diagonalSL a) = torusMap F K (a,1) := by
  rw [rankOneShortOrthogonal_apply, map_diagonalSL, map_diagonalSL,
    signTwist_diagonalSL, contragredient_diagonalSL, contragredient_diagonalSL]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [blockEmbedding, blockLinear, splitBlocks, D2Matrix.toOrthogonal,
      D2Matrix.onD, D2Matrix.coordinates, D2Matrix.matrixAction, diagonalSL,
      SpecialLinearGroup.diag2_inv, SpecialLinearGroup.diag2_coe',
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
      torusMap, torusWeights, diagonalEmbedding, diagonalLinear, sigmaUnit, baseUnit,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

set_option maxHeartbeats 3000000 in
-- The central-node diagonal is transported to the prescribed coordinate pair.
theorem long_diagonal_torus (b : Fˣ) :
    rankOneLongOrthogonal F K (diagonalSL b) = torusMap F K (1,b) := by
  change coordinateCycle * blockEmbedding (D2Matrix.toOrthogonal
    (1,contragredient (SpecialLinearGroup.map (algebraMap F K) (diagonalSL b))),1) * coordinateCycle⁻¹ = _
  rw [map_diagonalSL, contragredient_diagonalSL]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  rcases k with k|k <;> fin_cases k <;>
    simp [coordinateCycle, coordinateCycleLinear, blockEmbedding, blockLinear, splitBlocks,
      D2Matrix.toOrthogonal, D2Matrix.onD, D2Matrix.coordinates, D2Matrix.matrixAction,
      diagonalSL, SpecialLinearGroup.diag2_inv, SpecialLinearGroup.diag2_coe',
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
      torusMap, torusWeights, diagonalEmbedding, diagonalLinear, sigmaUnit, baseUnit,
      Subgroup.coe_mul, LinearEquiv.mul_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem torus_le_generated : torus F K ≤ generated F K := by
  rintro _ ⟨⟨a,b⟩,rfl⟩
  have hp : (a,b) = (a,1)*(1,b) := by simp
  rw [hp,map_mul,←short_diagonal_torus,←long_diagonal_torus]
  exact Subgroup.mul_mem _ (rankOneShortOrthogonal_mem F K _) (rankOneLongOrthogonal_mem F K _)

end Atlas.Triality
