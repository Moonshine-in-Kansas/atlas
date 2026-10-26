import Atlas.LinearGroups.Unitary.WittThree

/-! Base-field torus conjugation on the actual rank-three root matrices. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The embedded base-field rank-one torus, in the hyperbolic basis. -/
def torusThreeMatrix (t : K) : Matrix (Fin 3) (Fin 3) K := diagonal ![t,1,t⁻¹]

omit [Finite K] in
theorem torusThreeMatrix_det (t : K) (ht : t ≠ 0) : (torusThreeMatrix t).det = 1 := by
  simp [torusThreeMatrix, det_diagonal, Fin.prod_univ_succ, ht]

omit [Finite K] in
theorem torusThreeMatrix_inverse (t : K) (ht : t ≠ 0) :
    torusThreeMatrix t * torusThreeMatrix t⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torusThreeMatrix, ht]

theorem torusThreeMatrix_preserves (t : K) (ht : t ≠ 0)
    (hfix : conjugation F K t = t) (x y : Fin 3 → K) :
    hyperbolicThreeForm (F := F) (torusThreeMatrix t *ᵥ x) (torusThreeMatrix t *ᵥ y) =
      hyperbolicThreeForm (F := F) x y := by
  simp [torusThreeMatrix, hyperbolicThreeForm, mulVec, dotProduct, Fin.sum_univ_succ, map_mul, map_inv₀, hfix]
  field_simp

theorem torusThree_root_conjugation (t : K) (ht : t ≠ 0)
    (hfix : conjugation F K t = t) (a b : K) :
    torusThreeMatrix t * rootThreeMatrix (F := F) a b * torusThreeMatrix t⁻¹ =
      rootThreeMatrix (F := F) (t*a) (t^2*b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusThreeMatrix, rootThreeMatrix, mul_apply, Fin.sum_univ_succ,
      map_mul, hfix, ht] <;> ring

theorem rootThreeCondition_torus (t : K) (hfix : conjugation F K t = t)
    (a b : K) (hab : rootThreeCondition (F := F) a b) :
    rootThreeCondition (F := F) (t*a) (t^2*b) := by
  dsimp [rootThreeCondition] at *
  simp only [map_mul, map_pow, hfix]
  linear_combination t^2 * hab

theorem rootThreeCondition_inverse (hdeg : Module.finrank F K = 2) (a b : K)
    (hab : rootThreeCondition (F := F) a b) :
    rootThreeCondition (F := F) (-a) (-b-a*conjugation F K a) := by
  dsimp [rootThreeCondition] at *
  simp only [map_neg, map_sub, map_mul, conjugation_conjugation hdeg]
  linear_combination -hab
end Atlas.Unitary
