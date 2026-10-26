import Atlas.LinearGroups.Chevalley.Integral.GradedAdjoint
import Atlas.LinearGroups.Chevalley.TorusGlobal

/-! Conjugation and multiplication laws for the actual torus words in the
generated adjoint group. All coefficient rings are commutative, without
characteristic restrictions. -/
noncomputable section
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

theorem adjointTorus_val_geckWeightDiagonal (i : b.support) (t : Rˣ) :
    (adjointTorus P b R i t).val.val = geckWeightDiagonal P b R i t := by
  rw [adjointTorus_matrix]
  congr 1
  funext a
  cases a <;> simp [adjointTorusCoordinate, geckWeight]

theorem adjointTorus_mul_X (i j : b.support) (t : Rˣ) (s : R) :
    adjointTorus P b R i t * adjointX P b R j s =
      adjointX P b R j ((t ^ b.cartanMatrix j i).val * s) *
        adjointTorus P b R i t := by
  apply Subtype.ext
  apply Units.ext
  change (adjointTorus P b R i t).val.val * raisingExponential P b R j s =
    raisingExponential P b R j ((t ^ b.cartanMatrix j i).val * s) *
      (adjointTorus P b R i t).val.val
  rw [adjointTorus_val_geckWeightDiagonal]
  exact geckWeightDiagonal_raisingExponential P b R i j t s

theorem adjointTorus_mul_Y (i j : b.support) (t : Rˣ) (s : R) :
    adjointTorus P b R i t * adjointY P b R j s =
      adjointY P b R j ((t ^ (-b.cartanMatrix j i)).val * s) *
        adjointTorus P b R i t := by
  apply Subtype.ext
  apply Units.ext
  change (adjointTorus P b R i t).val.val * (loweringRootElement P b R j s).val =
    (loweringRootElement P b R j ((t ^ (-b.cartanMatrix j i)).val * s)).val *
      (adjointTorus P b R i t).val.val
  rw [loweringRootElement_val, loweringRootElement_val,
    adjointTorus_val_geckWeightDiagonal]
  exact geckWeightDiagonal_loweringExponential P b R i j t s

theorem adjointTorus_conjugate_X (i j : b.support) (t : Rˣ) (s : R) :
    adjointTorus P b R i t * adjointX P b R j s *
        (adjointTorus P b R i t)⁻¹ =
      adjointX P b R j ((t ^ b.cartanMatrix j i).val * s) := by
  rw [adjointTorus_mul_X, mul_assoc, mul_inv_cancel, mul_one]

theorem adjointTorus_conjugate_Y (i j : b.support) (t : Rˣ) (s : R) :
    adjointTorus P b R i t * adjointY P b R j s *
        (adjointTorus P b R i t)⁻¹ =
      adjointY P b R j ((t ^ (-b.cartanMatrix j i)).val * s) := by
  rw [adjointTorus_mul_Y, mul_assoc, mul_inv_cancel, mul_one]

theorem adjointTorus_mul (i : b.support) (t u : Rˣ) :
    adjointTorus P b R i (t*u) = adjointTorus P b R i t * adjointTorus P b R i u := by
  apply Subtype.ext
  apply Units.ext
  change (adjointTorus P b R i (t*u)).val.val =
    (adjointTorus P b R i t).val.val * (adjointTorus P b R i u).val.val
  rw [adjointTorus_matrix, adjointTorus_matrix, adjointTorus_matrix,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  cases a <;> simp [adjointTorusCoordinate, mul_zpow]

theorem adjointTorus_commute (i j : b.support) (t u : Rˣ) :
    Commute (adjointTorus P b R i t) (adjointTorus P b R j u) := by
  change adjointTorus P b R i t * adjointTorus P b R j u =
    adjointTorus P b R j u * adjointTorus P b R i t
  apply Subtype.ext
  apply Units.ext
  change (adjointTorus P b R i t).val.val * (adjointTorus P b R j u).val.val =
    (adjointTorus P b R j u).val.val * (adjointTorus P b R i t).val.val
  rw [adjointTorus_matrix, adjointTorus_matrix]
  exact (Matrix.commute_diagonal _ _).eq

end Atlas.Chevalley
