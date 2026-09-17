import Atlas.LinearAlgebra.QuadraticResidualReflection
import Atlas.LinearAlgebra.QuadraticWallDeterminant
import Atlas.LinearAlgebra.BilinearDeterminantTransport

/-! # Wall determinant factorization for anisotropic residual reflections -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
  (g : Q.IsometryEquiv Q) (u : residual Q g) (hu : Q u.val ≠ 0)

/-- Reflection at an anisotropic residual vector removes its quadratic square class. -/
theorem wallDeterminantClass_reflection_residual :
    wallDeterminantClass Q hQ g = Atlas.squareClass F (Units.mk0 (Q u.val) hu) *
      wallDeterminantClass Q hQ (reflectedIsometry Q g u.val hu) := by
  classical
  let h := reflectedIsometry Q g u.val hu
  let E := reflectedResidualEquiv Q g u hu
  let b := Module.finBasis F (residual Q h)
  let c := b.map E
  have hu' : wallForm Q g u u ≠ 0 := (wallForm_self Q g u) ▸ hu
  have hc := Atlas.Bilinear.linePerpForm_nondegenerate (wallForm Q g) u hu' c
    (wallForm_nondegenerate Q g hQ)
  have ht := Atlas.Bilinear.determinantClass_transport (wallForm Q h)
    (wallForm_nondegenerate Q h hQ) (Atlas.Bilinear.linePerpForm (wallForm Q g) u)
    hc E (fun x y => (reflected_wallForm Q g u hu x y).symm) b
  unfold wallDeterminantClass
  rw [Atlas.Bilinear.determinantClass_basis_independent_any (wallForm Q g)
    (wallForm_nondegenerate Q g hQ) (Module.finBasis F (residual Q g))
    (Atlas.Bilinear.lineBasis (wallForm Q g) u hu' c)]
  rw [Atlas.Bilinear.determinantClass_line]
  have hs : Units.mk0 (wallForm Q g u u) hu' = Units.mk0 (Q u.val) hu :=
    Units.ext (wallForm_self Q g u)
  rw [hs]
  exact congrArg (fun t => Atlas.squareClass F (Units.mk0 (Q u.val) hu) * t) ht

end Atlas.Quadratic
