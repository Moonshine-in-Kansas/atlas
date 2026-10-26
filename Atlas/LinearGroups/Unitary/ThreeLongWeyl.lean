import Atlas.LinearGroups.Unitary.ThreeBruhat

/-! The long-root Weyl element and the torus-producing Bruhat relation. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def longWeylThreeMatrix (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0,0,z; 0,1,0; -z⁻¹,0,0]

omit [Finite K] in
theorem longWeylThreeMatrix_inverse (z : K) (hz : z ≠ 0) :
    longWeylThreeMatrix z * longWeylThreeMatrix (-z) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longWeylThreeMatrix, mul_apply, Fin.sum_univ_succ, hz]

/-- The long-root Weyl element differs from the coordinate swap by an explicit torus. -/
theorem longWeylThreeMatrix_factor (z : K) (hz : z ≠ 0)
    (htrace : z + conjugation F K z = 0) :
    longWeylThreeMatrix z = fullTorusThreeMatrix (F := F) z * weylThreeMatrix := by
  have hs : conjugation F K z = -z := by linear_combination htrace
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longWeylThreeMatrix, fullTorusThreeMatrix, weylThreeMatrix, mul_apply,
      Fin.sum_univ_succ, hs, hz]

/-- The conjugated root parameters in the torus-producing relation are admissible. -/
theorem rootThreeCondition_longWeyl_left (_hdeg : Module.finrank F K = 2)
    (z : K) (htrace : z + conjugation F K z = 0)
    (a b : K) (hab : rootThreeCondition (F := F) a b) (hb : b ≠ 0) :
    rootThreeCondition (F := F) (-z*a/b) (-z^2/b) := by
  have hs : conjugation F K z = -z := by linear_combination htrace
  have hbar : conjugation F K b ≠ 0 := (map_ne_zero _).mpr hb
  dsimp [rootThreeCondition] at *
  simp only [map_div₀, map_mul, map_neg, map_pow, hs]
  field_simp
  linear_combination -(z^2) * hab

theorem rootThreeCondition_longWeyl_right (hdeg : Module.finrank F K = 2)
    (z : K) (htrace : z + conjugation F K z = 0)
    (a b : K) (hab : rootThreeCondition (F := F) a b) (hb : b ≠ 0) :
    rootThreeCondition (F := F) (-z*a/conjugation F K b) (-z^2/b) := by
  have hs : conjugation F K z = -z := by linear_combination htrace
  have hbar : conjugation F K b ≠ 0 := (map_ne_zero _).mpr hb
  dsimp [rootThreeCondition] at *
  simp only [map_div₀, map_mul, map_neg, map_pow, hs, conjugation_conjugation hdeg]
  field_simp
  linear_combination -(z^2) * hab

/-- An explicit word extracting every full-torus parameter from the root group
and the long-root Weyl element. -/
theorem longWeyl_three_bruhat (hdeg : Module.finrank F K = 2)
    (z : K) (hz : z ≠ 0) (htrace : z + conjugation F K z = 0)
    (a b : K) (hab : rootThreeCondition (F := F) a b) (hb : b ≠ 0) :
    longWeylThreeMatrix z * rootThreeMatrix (F := F) a b * longWeylThreeMatrix (-z) =
      rootThreeMatrix (F := F) (-z*a/b) (-z^2/b) *
        fullTorusThreeMatrix (F := F) (conjugation F K z / conjugation F K b) *
        longWeylThreeMatrix z *
        rootThreeMatrix (F := F) (-z*a/conjugation F K b) (-z^2/b) := by
  have hs : conjugation F K z = -z := by linear_combination htrace
  have hbar : conjugation F K b ≠ 0 := (map_ne_zero _).mpr hb
  have hab' : a * conjugation F K a + b + conjugation F K b = 0 := hab
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longWeylThreeMatrix, rootThreeMatrix, fullTorusThreeMatrix, mul_apply,
      vecMul, dotProduct, Fin.sum_univ_succ, map_div₀, map_neg,
      conjugation_conjugation hdeg, hs] <;>
    field_simp <;> (try simp only [true_or]) <;>
    first | (solve | ring) | (solve | linear_combination hab') |
      (solve | linear_combination -hab') | linear_combination z^2 * hab'
end Atlas.Unitary
