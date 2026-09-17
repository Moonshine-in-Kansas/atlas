import Atlas.LinearGroups.ReeG2.RootGroup
import Atlas.LinearGroups.ReeG2.Torus

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem torus_inv (m : ℕ) (l : Fˣ) : (torus m l)⁻¹ = torus m l⁻¹ :=
  ((torusHom (F := F) m).map_inv l).symm

/-- The explicit three characters for the upper triangular convention. -/
theorem torus_conjugate_root (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (l : Fˣ) (a b c : F) :
    (torus m l)⁻¹ * rootElement m a b c * torus m l =
      rootElement m (a * (theta F m (l : F))^3 / (l : F)^2)
        (b * (l : F) / (theta F m (l : F))^3) (c / (l : F)) := by
  rw [torus_inv]
  apply Units.ext
  change Matrix.diagonal (fun i => (torusDiagonal m l⁻¹ i : F)) *
    rootMatrix m a b c * Matrix.diagonal (fun i => (torusDiagonal m l i : F)) = _
  change _ = rootMatrix m _ _ _
  simp only [rootMatrix_expanded]
  have hl : (l : F) ≠ 0 := Units.ne_zero l
  have ht : theta F m (l : F) ≠ 0 := (map_ne_zero (theta F m)).2 hl
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [torusDiagonal, rootExpanded, -theta_apply, theta_square_cube hcard] <;>
    field_simp <;> ring
end Atlas.ReeG2
