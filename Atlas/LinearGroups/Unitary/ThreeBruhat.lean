import Atlas.LinearGroups.Unitary.ThreeTorus

/-! Concrete rank-three Bruhat relations. These are matrix identities for the
retained field and involution, with every root parameter condition proved. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def weylThreeMatrix : Matrix (Fin 3) (Fin 3) K := !![0,0,1; 0,-1,0; 1,0,0]

def fullTorusThreeMatrix (t : K) : Matrix (Fin 3) (Fin 3) K :=
  diagonal ![t, conjugation F K t / t, (conjugation F K t)⁻¹]

theorem fullTorusThreeMatrix_det (t : K) (ht : t ≠ 0) :
    (fullTorusThreeMatrix (F := F) t).det = 1 := by
  have hbar : conjugation F K t ≠ 0 := (map_ne_zero _).mpr ht
  simp [fullTorusThreeMatrix, det_diagonal, Fin.prod_univ_succ]
  field_simp

theorem fullTorusThreeMatrix_preserves (hdeg : Module.finrank F K = 2)
    (t : K) (ht : t ≠ 0) (x y : Fin 3 → K) :
    hyperbolicThreeForm (F := F) (fullTorusThreeMatrix (F := F) t *ᵥ x)
      (fullTorusThreeMatrix (F := F) t *ᵥ y) = hyperbolicThreeForm (F := F) x y := by
  have hbar : conjugation F K t ≠ 0 := (map_ne_zero _).mpr ht
  simp [fullTorusThreeMatrix, hyperbolicThreeForm, mulVec, dotProduct,
    Fin.sum_univ_succ, map_mul, map_div₀, map_inv₀, conjugation_conjugation hdeg]
  field_simp

/-- The left root parameters in the Bruhat relation satisfy the actual trace equation. -/
theorem rootThreeCondition_bruhat_left (_hdeg : Module.finrank F K = 2)
    (a b : K) (hab : rootThreeCondition (F := F) a b) (hb : b ≠ 0) :
    rootThreeCondition (F := F) (-a/b) (1/b) := by
  have hbar : conjugation F K b ≠ 0 := (map_ne_zero _).mpr hb
  dsimp [rootThreeCondition] at *
  simp only [map_div₀, map_neg, map_one]
  field_simp
  linear_combination hab

/-- The right root parameters in the Bruhat relation satisfy the actual trace equation. -/
theorem rootThreeCondition_bruhat_right (hdeg : Module.finrank F K = 2)
    (a b : K) (hab : rootThreeCondition (F := F) a b) (hb : b ≠ 0) :
    rootThreeCondition (F := F) (-a/conjugation F K b) (1/b) := by
  have hbar : conjugation F K b ≠ 0 := (map_ne_zero _).mpr hb
  dsimp [rootThreeCondition] at *
  simp only [map_div₀, map_neg, map_one, conjugation_conjugation hdeg]
  field_simp
  linear_combination hab

/-- Explicit big-cell factorization; it is not an assumed group decomposition. -/
theorem three_bruhat_matrix (hdeg : Module.finrank F K = 2)
    (a b : K) (hab : rootThreeCondition (F := F) a b) (hb : b ≠ 0) :
    weylThreeMatrix * rootThreeMatrix (F := F) a b * weylThreeMatrix =
      rootThreeMatrix (F := F) (-a/b) (1/b) *
        fullTorusThreeMatrix (F := F) (conjugation F K b)⁻¹ *
        weylThreeMatrix * rootThreeMatrix (F := F) (-a/conjugation F K b) (1/b) := by
  have hbar : conjugation F K b ≠ 0 := (map_ne_zero _).mpr hb
  have hab' : a * conjugation F K a + b + conjugation F K b = 0 := hab
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylThreeMatrix, rootThreeMatrix, fullTorusThreeMatrix, mul_apply, vecMul, dotProduct,
      Fin.sum_univ_succ, map_div₀, map_neg, map_inv₀, conjugation_conjugation hdeg] <;>
    field_simp <;> first | (solve | ring) | (solve | linear_combination hab') | linear_combination -hab'
end Atlas.Unitary
