import Atlas.Algebra.SplitOctonion.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.StdBasis

namespace Atlas.SplitOctonion
variable {F : Type*} [CommRing F]

/-- Product preservation is determined by the 64 standard basis pairs. -/
theorem map_mul_of_basis (g : Carrier F →ₗ[F] Carrier F)
    (h : ∀ i j, g (mul (basisVector i) (basisVector j)) =
      mul (g (basisVector i)) (g (basisVector j))) :
    ∀ a b, g (mul a b) = mul (g a) (g b) := by
  have he : multiplication.compr₂ g = multiplication.compl₁₂ g g := by
    apply (Pi.basisFun F (Fin 8)).ext
    intro i
    apply (Pi.basisFun F (Fin 8)).ext
    intro j
    simpa [multiplication, Pi.basisFun_apply, basisVector] using h i j
  intro a b
  exact congrArg (fun f : Carrier F →ₗ[F] Carrier F →ₗ[F] Carrier F => f a b) he

/-- Equality of coordinate linear maps is determined by eight images. -/
theorem linearMap_ext (f g : Carrier F →ₗ[F] Carrier F)
    (h : ∀ i, f (basisVector i) = g (basisVector i)) : f = g :=
  (Pi.basisFun F (Fin 8)).ext (fun i => by simpa [Pi.basisFun_apply, basisVector] using h i)
end Atlas.SplitOctonion
