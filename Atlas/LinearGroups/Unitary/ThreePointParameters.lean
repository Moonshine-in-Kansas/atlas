import Atlas.LinearGroups.Unitary.GenerationThree

/-! Explicit affine parameters for all isotropic points off the first line in
hyperbolic dimension three. These are coordinates on the actual form, not an
assumed permutation action. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- An isotropic vector with last coordinate zero lies on the first line. -/
theorem three_isotropic_last_zero (x : Fin 3 → K)
    (hx : hyperbolicThreeForm (F := F) x x = 0) (hlast : x 2 = 0) :
    x = x 0 • Pi.single 0 1 := by
  have hmid : x 1 = 0 := by
    have he : x 1 * conjugation F K (x 1) = 0 := by
      simpa [hyperbolicThreeForm, hlast] using hx
    rcases mul_eq_zero.mp he with he | he
    · exact he
    · exact (map_eq_zero _).mp he
  ext i
  fin_cases i <;> simp [Pi.single_apply, hmid, hlast]

/-- Normalize the last coordinate: precisely the root-group parameter equation. -/
theorem three_isotropic_parameters (hdeg : Module.finrank F K = 2)
    (x : Fin 3 → K) (hx : hyperbolicThreeForm (F := F) x x = 0) (hlast : x 2 ≠ 0) :
    rootThreeCondition (F := F) (x 1 / x 2) (x 0 / x 2) ∧
      x = x 2 • (rootThreeMatrix (F := F) (x 1 / x 2) (x 0 / x 2) *ᵥ Pi.single 2 1) := by
  have hb : conjugation F K (x 2) ≠ 0 := (map_ne_zero _).mpr hlast
  constructor
  · dsimp [rootThreeCondition]
    simp only [map_div₀]
    field_simp
    dsimp [hyperbolicThreeForm] at hx
    linear_combination hx
  · rw [mulVec_single_one]
    ext i
    fin_cases i <;> simp [rootThreeMatrix, hlast, mul_div_cancel₀]

/-- The displayed affine vectors are isotropic exactly for admissible root parameters. -/
theorem three_affine_isotropic_iff (a b : K) :
    hyperbolicThreeForm (F := F) ![b,a,1] ![b,a,1] = 0 ↔
      rootThreeCondition (F := F) a b := by
  simp [hyperbolicThreeForm, rootThreeCondition, add_comm, add_left_comm, add_assoc]
end Atlas.Unitary
