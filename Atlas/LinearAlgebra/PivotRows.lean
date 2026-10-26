import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section
namespace Atlas.LinearAlgebra
open Matrix
open scoped Matrix

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- A unit determinant on chosen columns makes coefficient synthesis injective,
including over rings with zero divisors. -/
theorem pivotRows_injective (rows : Matrix ι κ R) (columns : ι → κ)
    (hdet : IsUnit (rows.submatrix id columns).det) :
    Function.Injective (fun a : ι → R => a ᵥ* rows) := by
  intro a b h
  apply Matrix.vecMul_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det (rows.submatrix id columns)).mpr hdet)
  funext i
  exact congrFun h (columns i)

/-- A triangular minor with diagonal one is a structural pivot certificate. -/
theorem pivotRows_injective_of_triangular [LinearOrder ι]
    (rows : Matrix ι κ R) (columns : ι → κ)
    (htri : (rows.submatrix id columns).IsUpperTriangular)
    (hdiag : ∀ i, rows i (columns i) = 1) :
    Function.Injective (fun a : ι → R => a ᵥ* rows) := by
  apply pivotRows_injective rows columns
  rw [Matrix.det_of_isUpperTriangular htri]
  simpa [Matrix.submatrix, hdiag] using (isUnit_one : IsUnit (1 : R))

/-- Injectively parameterized combinations contained in a code give a cardinal lower bound. -/
theorem pivotRows_card_le {S : Type*} [Finite S] [Finite κ] [Finite R]
    (C : Submodule R (κ → R)) (rows : Matrix ι κ R) (columns : ι → κ)
    (hdet : IsUnit (rows.submatrix id columns).det)
    (coefficients : S → (ι → R)) (hcoeff : Function.Injective coefficients)
    (hmem : ∀ s, coefficients s ᵥ* rows ∈ C) : Nat.card S ≤ Nat.card C := by
  apply Nat.card_le_card_of_injective (f := fun s => (⟨coefficients s ᵥ* rows,hmem s⟩ : C))
  intro s t h
  apply hcoeff
  exact pivotRows_injective rows columns hdet (congrArg Subtype.val h)

end Atlas.LinearAlgebra
