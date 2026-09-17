import Atlas.LinearAlgebra.QuadraticResidual
import Atlas.LinearAlgebra.BilinearDeterminantClass

/-! # The intrinsic determinant class of Wall's residual pairing

This file defines the determinant-class function. Multiplicativity is a separate
obligation; no spinor-norm homomorphism is asserted here.
-/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

def wallDeterminantClass (g : Q.IsometryEquiv Q) : Atlas.SquareClass F :=
  Atlas.Bilinear.determinantClass (wallForm Q g) (wallForm_nondegenerate Q g hQ)
    (Module.finBasis F (residual Q g))

/-- Any ordered basis of the residual space computes the same determinant class. -/
theorem wallDeterminantClass_basis (g : Q.IsometryEquiv Q)
    (b : Module.Basis (Fin (Module.finrank F (residual Q g))) F (residual Q g)) :
    wallDeterminantClass Q hQ g =
      Atlas.Bilinear.determinantClass (wallForm Q g) (wallForm_nondegenerate Q g hQ) b :=
  Atlas.Bilinear.determinantClass_basis_independent _ _ _ b

end Atlas.Quadratic
