import Atlas.Algebra.Albert.ScalarExtension
import Mathlib.LinearAlgebra.StdBasis

noncomputable section
namespace Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R]

theorem coordinate_basisVector (i : Coordinate) :
    coordinateEquiv (basisVector i : Carrier F) = Pi.single i 1 := by
  funext j; cases j <;> rfl

theorem map_basisVector (f : F →+* R) (i : Coordinate) :
    map f (basisVector i) = basisVector i := by
  apply coordinateEquiv.injective
  rw [coordinate_map, coordinate_basisVector, coordinate_basisVector]
  funext j
  simp [Pi.single_apply, apply_ite f]

theorem linearMap_ext_basis (f g : Carrier F →ₗ[F] Carrier F)
    (h : ∀ i : Coordinate, f (basisVector i) = g (basisVector i)) : f = g := by
  have hh : f.comp coordinateEquiv.symm.toLinearMap = g.comp coordinateEquiv.symm.toLinearMap := by
    apply (Pi.basisFun F Coordinate).ext
    intro i
    have hb : coordinateEquiv.symm (Pi.single i (1 : F)) = basisVector i := by
      apply coordinateEquiv.injective
      rw [LinearEquiv.apply_symm_apply, coordinate_basisVector]
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, hb] using h i
  apply LinearMap.ext
  intro x
  simpa using congrArg (fun f : (Coordinate → F) →ₗ[F] Carrier F => f (coordinateEquiv x)) hh

theorem scalarExtension_eq (g : Carrier F ≃ₗ[F] Carrier F) (f : F →+* R)
    (h : Carrier R →ₗ[R] Carrier R)
    (hn : ∀ x : Carrier F, h (map f x) = map f (g x)) : scalarExtension g f = h := by
  apply linearMap_ext_basis
  intro i
  rw [← map_basisVector f i, scalarExtension_map, hn]

theorem substitute_normPolynomial (g : Carrier F ≃ₗ[F] Carrier F) :
    Atlas.PolynomialLinear.substitute (matrixRepresentation g).val normPolynomial =
      norm (scalarExtension g MvPolynomial.C universalVector) := by
  have h := eval₂_normPolynomial (MvPolynomial.C : F →+* MvPolynomial Coordinate F)
    (scalarExtension g MvPolynomial.C universalVector)
  rw [scalarExtension_coordinates] at h
  have hx : coordinateEquiv (universalVector (F := F)) = MvPolynomial.X := by
    funext i; cases i <;> rfl
  rw [hx] at h
  exact h

def ofUniversalNorm (g : Carrier F ≃ₗ[F] Carrier F) (hu : g unit = unit)
    (hn : norm (scalarExtension g MvPolynomial.C universalVector) = normPolynomial) :
    polynomialStabilizer (F := F) :=
  ⟨g, (mem_polynomialStabilizer g).mpr ⟨(substitute_normPolynomial g).trans hn, hu⟩⟩

end Atlas.Albert
