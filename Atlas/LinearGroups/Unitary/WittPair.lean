import Atlas.LinearGroups.Unitary.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! An explicit hyperbolic basis for the standard Hermitian plane in every
finite characteristic. Norm and trace surjectivity replace division by two. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Parameters for a genuine hyperbolic pair; the trace condition is valid in
characteristic two as well as odd characteristic. -/
theorem exists_witt_parameters (hdeg : Module.finrank F K = 2) :
    ∃ a b : K, a * conjugation F K a = -1 ∧ b + conjugation F K b = 1 := by
  obtain ⟨a, ha⟩ := norm_surjective F K (-1)
  obtain ⟨b, hb⟩ := trace_surjective F K 1
  refine ⟨a, b, ?_, ?_⟩
  · rw [← norm_formula hdeg, ha, map_neg, map_one]
  · rw [← trace_formula hdeg, hb, map_one]

/-- Columns (1,a) and (1-b,-ba), not merely an abstract form of equal dimension. -/
def wittPlaneMatrix (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, 1 - b; a, -b * a]

omit [Finite K] in
theorem wittPlaneMatrix_det (a b : K) : (wittPlaneMatrix a b).det = -a := by
  rw [wittPlaneMatrix, Matrix.det_fin_two]
  dsimp
  ring

/-- The actual hyperbolic-coordinate form, linear in the first slot. -/
def hyperbolicPlaneForm (x y : Fin 2 → K) : K :=
  x 0 * conjugation F K (y 1) + x 1 * conjugation F K (y 0)

theorem wittPlaneMatrix_preserves (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (x y : Fin 2 → K) :
    hermitian F K (wittPlaneMatrix a b *ᵥ x) (wittPlaneMatrix a b *ᵥ y) =
      hyperbolicPlaneForm (F := F) x y := by
  have ha' : a * conjugation F K a + 1 = 0 := by rw [ha]; ring
  have hb' : conjugation F K b = 1 - b := by linear_combination hb
  simp only [hermitian, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
    wittPlaneMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_add, map_mul, map_neg, map_sub, map_one,
    hyperbolicPlaneForm]
  rw [hb']
  linear_combination
    (x 0 * conjugation F K (y 0) + (b - 1) * x 0 * conjugation F K (y 1) -
      b * x 1 * conjugation F K (y 0) -
      b * (b - 1) * x 1 * conjugation F K (y 1)) * ha'

/-- The actual invertible coordinate change realizing the hyperbolic plane. -/
def wittPlaneEquiv (a b : K) (ha : a * conjugation F K a = -1) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  Matrix.toLinearEquiv (Pi.basisFun K (Fin 2)) (wittPlaneMatrix a b) (by
    rw [wittPlaneMatrix_det]
    apply isUnit_iff_ne_zero.mpr
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    exact neg_ne_zero.mpr ha0)

theorem wittPlaneEquiv_preserves (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (x y : Fin 2 → K) :
    hermitian F K (wittPlaneEquiv a b ha x) (wittPlaneEquiv a b ha y) =
      hyperbolicPlaneForm (F := F) x y := by
  simpa [wittPlaneEquiv, Matrix.toLinearEquiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply] using
    wittPlaneMatrix_preserves a b ha hb x y

/-- The chosen standard Hermitian plane actually admits a hyperbolic basis. -/
theorem exists_wittPlaneEquiv (hdeg : Module.finrank F K = 2) :
    ∃ e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K),
      ∀ x y, hermitian F K (e x) (e y) = hyperbolicPlaneForm (F := F) x y := by
  obtain ⟨a, b, ha, hb⟩ := exists_witt_parameters hdeg
  exact ⟨wittPlaneEquiv a b ha, wittPlaneEquiv_preserves a b ha hb⟩
end Atlas.Unitary
