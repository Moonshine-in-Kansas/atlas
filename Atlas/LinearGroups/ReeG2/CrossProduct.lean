import Atlas.LinearGroups.ReeG2.PointCompatibility
import Atlas.LinearGroups.ReeG2.InvariantForm

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The alternating cross product in the fixed seven-coordinate basis. -/
def crossProduct (v w : Vector F) : Vector F :=
  ![wedgeCoordinate v w 0 3 - wedgeCoordinate v w 1 2,
    -wedgeCoordinate v w 0 4 - wedgeCoordinate v w 1 3,
    wedgeCoordinate v w 0 5 - wedgeCoordinate v w 2 3,
    wedgeCoordinate v w 0 6 - wedgeCoordinate v w 1 5 - wedgeCoordinate v w 2 4,
    wedgeCoordinate v w 1 6 - wedgeCoordinate v w 3 4,
    -wedgeCoordinate v w 2 6 - wedgeCoordinate v w 3 5,
    wedgeCoordinate v w 3 6 - wedgeCoordinate v w 4 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Coordinate expansion of the seven bilinear identities.
theorem alpha_preserves_crossProduct (m : ℕ) (x : F) (v w : Vector F) :
    crossProduct (rowEquiv (alpha m x) v) (rowEquiv (alpha m x) w) =
      rowEquiv (alpha m x) (crossProduct v w) := by
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, -theta_apply] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Coordinate expansion of the seven bilinear identities.
theorem beta_preserves_crossProduct (m : ℕ) (x : F) (v w : Vector F) :
    crossProduct (rowEquiv (beta m x) v) (rowEquiv (beta m x) w) =
      rowEquiv (beta m x) (crossProduct v w) := by
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, -theta_apply] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Coordinate expansion of the seven bilinear identities.
theorem gamma_preserves_crossProduct (m : ℕ) (x : F) (v w : Vector F) :
    crossProduct (rowEquiv (gamma m x) v) (rowEquiv (gamma m x) w) =
      rowEquiv (gamma m x) (crossProduct v w) := by
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, -theta_apply] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Seven diagonal-weight identities, with nonzero unit denominators.
theorem torus_preserves_crossProduct (m : ℕ) (l : Fˣ) (v w : Vector F) :
    crossProduct (rowEquiv (torus m l) v) (rowEquiv (torus m l) w) =
      rowEquiv (torus m l) (crossProduct v w) := by
  have hl := Units.ne_zero l
  have ht : theta F m (l : F) ≠ 0 := (map_ne_zero (theta F m)).mpr hl
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit,
      torusDiagonal, Matrix.vecMul_diagonal, -theta_apply] <;>
    field_simp <;> ring

theorem upsilon_preserves_crossProduct (v w : Vector F) :
    crossProduct (rowEquiv (upsilon : Ambient F) v) (rowEquiv upsilon w) =
      rowEquiv upsilon (crossProduct v w) := by
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, upsilon, upsilonMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring

end Atlas.ReeG2

