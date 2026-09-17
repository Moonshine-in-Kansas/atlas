import Atlas.Lattices.EisensteinComparisonSpace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators QuadraticAlgebra Matrix

/-- Three times the marked Fourier operator. It includes the phase and coordinate
corrections required by the retained ternary code and integral glue. -/
def eisensteinFourierNumerator : Matrix (Fin 12) (Fin 12) Eisenstein :=
  ![![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 2⟩, ⟨-2, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 2⟩, ⟨1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, 1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

def eisensteinFourierMatrix : Matrix (Fin 12) (Fin 12) EisensteinRational := fun i j =>
  (1/3 : ℚ) • eisensteinToRational (eisensteinFourierNumerator i j)

def eisensteinFourierColumn : Fin 12 → Fin 4 := ![0,0,0,1,1,1,2,3,2,3,3,2]

def eisensteinFourierRow : Fin 12 → Fin 3 := ![0,1,2,0,1,2,0,0,1,1,2,2]

def eisensteinFourierOutputPosition : Fin 12 → Fin 12 := ![0,1,2,3,5,4,11,10,8,7,9,6]

def eisensteinFourierOutputPhase : Fin 12 → Fin 3 := ![0,0,0,0,1,2,0,0,2,2,1,1]

/-- Exact block-Fourier factorization, including the required marking correction. -/
theorem eisensteinFourier_marking : ∀ i j : Fin 12,
    eisensteinFourierNumerator (eisensteinFourierOutputPosition i) j =
    if eisensteinFourierColumn i = eisensteinFourierColumn j then
      (![1,-1,-1,1] (eisensteinFourierColumn i) : Eisenstein) *
      eisensteinOmega ^ (eisensteinFourierOutputPhase i).val * eisensteinTheta *
      eisensteinOmega ^ ((eisensteinFourierRow i).val*(eisensteinFourierRow j).val%3)
    else 0 := by
  decide +kernel

theorem eisensteinFourier_unitary_left :
    eisensteinFourierMatrix.conjTranspose * eisensteinFourierMatrix = 1 := by
  decide +kernel

theorem eisensteinFourier_unitary_right :
    eisensteinFourierMatrix * eisensteinFourierMatrix.conjTranspose = 1 := by
  decide +kernel

noncomputable def eisensteinFourierLinear :
    EisensteinRationalCoordinates ≃ₗ[EisensteinRational] EisensteinRationalCoordinates :=
  Matrix.toLin'OfInv eisensteinFourier_unitary_left eisensteinFourier_unitary_right

noncomputable def eisensteinFourier :
    EisensteinRationalCoordinates ≃ₗ[ℚ] EisensteinRationalCoordinates :=
  eisensteinFourierLinear.restrictScalars ℚ

@[simp] theorem eisensteinFourier_apply (z : EisensteinRationalCoordinates) :
    eisensteinFourier z = eisensteinFourierMatrix *ᵥ z := rfl

@[simp] theorem eisensteinFourier_symm_apply (z : EisensteinRationalCoordinates) :
    eisensteinFourier.symm z = eisensteinFourierMatrix.conjTranspose *ᵥ z := rfl

theorem eisensteinFourier_hermitian (z w : EisensteinRationalCoordinates) :
    eisensteinHermitian (eisensteinFourier z) (eisensteinFourier w) =
      eisensteinHermitian z w := by
  unfold eisensteinHermitian
  congr 1
  change dotProduct (star (eisensteinFourierMatrix *ᵥ z))
    (eisensteinFourierMatrix *ᵥ w) = dotProduct (star z) w
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    eisensteinFourier_unitary_left, Matrix.vecMul_one]

end Atlas.Lattices
