import Mathlib.Algebra.MvPolynomial.CommRing
import Atlas.Algebra.Albert.PolynomialStabilizer

noncomputable section
namespace Atlas.Albert
open Matrix
variable {F R : Type*} [CommRing F] [CommRing R]

theorem eval₂_normPolynomial (f : F →+* R) (x : Carrier R) :
    MvPolynomial.eval₂Hom f (coordinateEquiv x) (normPolynomial (F := F)) = norm x := by
  simp [normPolynomial, universalVector, norm, SplitOctonion.norm,
    SplitOctonion.trace, SplitOctonion.mul, coordinateEquiv]
  rfl

def scalarExtension (g : Carrier F ≃ₗ[F] Carrier F) (f : F →+* R) :
    Carrier R →ₗ[R] Carrier R :=
  coordinateEquiv.symm.toLinearMap.comp
    ((Matrix.toLin' ((matrixRepresentation g).val.map f)).comp coordinateEquiv.toLinearMap)

theorem scalarExtension_coordinates (g : Carrier F ≃ₗ[F] Carrier F)
    (f : F →+* R) (x : Carrier R) :
    coordinateEquiv (scalarExtension g f x) =
      (matrixRepresentation g).val.map f *ᵥ coordinateEquiv x := by
  simp [scalarExtension, Matrix.toLin'_apply]

theorem coordinate_map (f : F →+* R) (x : Carrier F) :
    coordinateEquiv (map f x) = f ∘ coordinateEquiv x := by
  funext i; cases i <;> rfl

theorem scalarExtension_map (g : Carrier F ≃ₗ[F] Carrier F)
    (f : F →+* R) (x : Carrier F) : scalarExtension g f (map f x) = map f (g x) := by
  apply coordinateEquiv.injective
  rw [scalarExtension_coordinates, coordinate_map, coordinate_map]
  funext i
  exact (f.map_mulVec (matrixRepresentation g).val (coordinateEquiv x) i).symm.trans
    (congrArg (fun y : Coordinate → F => f (y i)) (matrixRepresentation_apply g x))

theorem scalarExtension_unit (g : polynomialStabilizer (F := F)) (f : F →+* R) :
    scalarExtension g.val f unit = unit := by
  rw [← map_unit f, scalarExtension_map, stabilizer_unit]

theorem scalarExtension_norm (g : polynomialStabilizer (F := F))
    (f : F →+* R) (x : Carrier R) : norm (scalarExtension g.val f x) = norm x := by
  have h := congrArg (MvPolynomial.eval₂Hom f (coordinateEquiv x)) g.property.1
  rw [Atlas.PolynomialLinear.eval₂_substitute,
    ← scalarExtension_coordinates, eval₂_normPolynomial, eval₂_normPolynomial] at h
  exact h

end Atlas.Albert
