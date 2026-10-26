import Atlas.LinearGroups.Unitary.WittPair

/-! Explicit rank-three unitary root matrices. These identities do not assert
transvection generation; that theorem must separately exclude the binary case. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The hyperbolic pair and norm-one middle coordinate in dimension three. -/
def hyperbolicThreeForm (x y : Fin 3 → K) : K :=
  x 0 * conjugation F K (y 2) + x 1 * conjugation F K (y 1) +
    x 2 * conjugation F K (y 0)

/-- The actual trace/norm parameter condition of the three-dimensional root group. -/
def rootThreeCondition (a b : K) : Prop :=
  a * conjugation F K a + b + conjugation F K b = 0

/-- Explicit positive unipotent matrices, before standard-coordinate transfer. -/
def rootThreeMatrix (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, -conjugation F K a, b; 0, 1, a; 0, 0, 1]

theorem rootThreeMatrix_mul (a b c d : K) :
    rootThreeMatrix (F := F) a b * rootThreeMatrix (F := F) c d =
      rootThreeMatrix (F := F) (a+c) (b+d-conjugation F K a*c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootThreeMatrix, mul_apply, Fin.sum_univ_succ] <;> ring

theorem rootThreeCondition_mul (hdeg : Module.finrank F K = 2) (a b c d : K)
    (hab : rootThreeCondition (F := F) a b) (hcd : rootThreeCondition (F := F) c d) :
    rootThreeCondition (F := F) (a+c) (b+d-conjugation F K a*c) := by
  dsimp [rootThreeCondition] at *
  simp only [map_add, map_sub, map_mul, conjugation_conjugation hdeg]
  linear_combination hab + hcd

@[simp] theorem rootThreeMatrix_zero : rootThreeMatrix (F := F) (0 : K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootThreeMatrix]

theorem rootThreeMatrix_inverse (a b : K) :
    rootThreeMatrix (F := F) a b *
      rootThreeMatrix (F := F) (-a) (-b-a*conjugation F K a) = 1 := by
  rw [rootThreeMatrix_mul]
  convert rootThreeMatrix_zero (F := F) (K := K) using 2 <;> ring

theorem rootThreeMatrix_det (a b : K) : (rootThreeMatrix (F := F) a b).det = 1 := by
  simp [rootThreeMatrix, det_fin_three]

theorem rootThreeMatrix_preserves (hdeg : Module.finrank F K = 2) (a b : K)
    (hab : rootThreeCondition (F := F) a b) (x y : Fin 3 → K) :
    hyperbolicThreeForm (F := F) (rootThreeMatrix (F := F) a b *ᵥ x)
      (rootThreeMatrix (F := F) a b *ᵥ y) = hyperbolicThreeForm (F := F) x y := by
  dsimp [rootThreeCondition] at hab
  simp [hyperbolicThreeForm, rootThreeMatrix, mulVec, dotProduct,
    Fin.sum_univ_succ, map_add, map_mul, conjugation_conjugation hdeg]
  <;> linear_combination x 2 * conjugation F K (y 2) * hab

/-- The trace-zero central root matrices retain the additive parameter law. -/
theorem rootThreeMatrix_center_commutes (a b z : K) :
    rootThreeMatrix (F := F) 0 z * rootThreeMatrix (F := F) a b =
      rootThreeMatrix (F := F) a b * rootThreeMatrix (F := F) 0 z := by
  rw [rootThreeMatrix_mul, rootThreeMatrix_mul]
  simp [add_comm]

/-- Root parameters are retained faithfully by the explicit matrices. -/
theorem rootThreeMatrix_injective : Function.Injective
    (fun p : K × K => rootThreeMatrix (F := F) p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun M => M 1 2) h
  · exact congrArg (fun M => M 0 2) h

/-- Every first parameter admits a genuine trace-compatible second parameter. -/
theorem exists_rootThree_parameter (hdeg : Module.finrank F K = 2) (a : K) :
    ∃ b : K, rootThreeCondition (F := F) a b := by
  obtain ⟨b, hb⟩ := trace_surjective F K (-norm F K a)
  have h := congrArg (algebraMap F K) hb
  rw [trace_formula hdeg, map_neg, norm_formula hdeg] at h
  refine ⟨b, ?_⟩
  dsimp [rootThreeCondition]
  exact (add_assoc _ _ _).trans (by rw [h, add_neg_cancel])
end Atlas.Unitary
