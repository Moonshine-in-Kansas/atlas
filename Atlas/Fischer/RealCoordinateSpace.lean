import Atlas.Fischer.RationalCoordinateBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.Real.Basic

noncomputable section
namespace Atlas.Fischer
open scoped TensorProduct

/-- Real scalar extension of the actual underlying rational algebra space. -/
abbrev RealCoordinates := ℝ ⊗[ℚ] Coordinates

def realCoordinateBasis : Module.Basis RationalCoordinateIndex ℝ RealCoordinates :=
  rationalCoordinateBasis.baseChange ℝ

def realCoordinateEquiv : RealCoordinates ≃ₗ[ℝ] (RationalCoordinateIndex → ℝ) :=
  realCoordinateBasis.equivFun

/-- Real coordinates of a pure tensor retain the actual rational coordinates. -/
theorem realCoordinateEquiv_tmul (a : ℝ) (x : Coordinates) (p : RationalCoordinateIndex) :
    realCoordinateEquiv (a ⊗ₜ[ℚ] x) p = (rationalCoordinateEquiv x p : ℝ) * a := by
  change (rationalCoordinateBasis.baseChange ℝ).equivFun (a ⊗ₜ[ℚ] x) p = _
  rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
  change (rationalCoordinateEquiv x p) • a = _
  exact Rat.smul_def _ _

theorem realCoordinates_finrank : Module.finrank ℝ RealCoordinates = 1566 := by
  rw [realCoordinateEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  change Fintype.card (CoordinateIndex × Fin 2) = 1566
  rw [Fintype.card_prod, coordinateIndex_card, Fintype.card_fin]

theorem rational_real_extension_injective :
    Function.Injective (fun x : Coordinates => (1 : ℝ) ⊗ₜ[ℚ] x) := by
  intro x y h
  apply rationalCoordinateEquiv.injective
  funext p
  have hh := congrArg (fun z => realCoordinateEquiv z p) h
  simp only [realCoordinateEquiv_tmul, mul_one] at hh
  exact Rat.cast_injective hh

end Atlas.Fischer
