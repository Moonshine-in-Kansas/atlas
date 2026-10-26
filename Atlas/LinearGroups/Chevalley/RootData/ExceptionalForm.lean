import Atlas.LinearGroups.Chevalley.RootData.FiniteSimplyLaced
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Cartan

/-! Integral Cartan forms for the exceptional simply-laced data. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Atlas.Chevalley.ExceptionalData
open FiniteSimplyLaced

def form (n : ℕ) : Lattice n →ₗ[ℤ] Module.Dual ℤ (Lattice n) :=
  Matrix.toBilin' (CartanMatrix.E n)

theorem form_symm (n : ℕ) (x y : Lattice n) : form n x y = form n y x := by
  exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr (CartanMatrix.E_isSymm n)).eq x y

theorem form_injective (n : ℕ) (h3 : 3 ≤ n) (h9 : n < 9) :
    Function.Injective (form n) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.separatingLeft_iff_ker_eq_bot.mp
  apply (LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
    (CartanMatrix.E n) ?_).1
  rw [CartanMatrix.E_det h3]
  omega

theorem form_single_left (n : ℕ) (i : Fin n) (x : Lattice n) :
    form n (Pi.single i 1) x = ∑ j, CartanMatrix.E n i j * x j := by
  simp [form, Matrix.toBilin'_apply, Pi.single_apply]

theorem reflectVector_eq_update (n : ℕ) (i : Fin n) (x : Lattice n) :
    reflectVector (form n) i x =
      Function.update x i (x i - ∑ j, CartanMatrix.E n i j * x j) := by
  funext k
  by_cases h : k = i
  · subst k
    simp [reflectVector, form_single_left]
  · simp [reflectVector, form_single_left, h]

end Atlas.Chevalley.ExceptionalData

