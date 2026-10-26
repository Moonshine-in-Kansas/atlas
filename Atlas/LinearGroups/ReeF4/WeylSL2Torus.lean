import Atlas.LinearGroups.ReeF4.WeylSL2Parameters
import Atlas.LinearGroups.ReeF4.TorusFieldWeights
import Atlas.LinearGroups.ReeF4.TorusGroup

/-! The actual long-root parameter scaling under the retained source torus. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

def longSL2DiagonalWeights {G : Type*} [CommGroup G] (a b : G) : ShortRootLabel → G :=
  fun r =>
    (![![a, a⁻¹*b, a⁻¹*b⁻¹, a⁻¹, a, a*b, a*b⁻¹, a⁻¹],
       ![1, b, b⁻¹, a^2, (a⁻¹)^2, b, b⁻¹, 1],
       ![a⁻¹, a*b, a*b⁻¹, a⁻¹, a, a⁻¹*b, a⁻¹*b⁻¹, a]]) r.1 r.2

variable {F : Type*} [Field F] [CharP F 2]

def longSL2Diagonal (a b : Fˣ) : TraceZero F ≃ₗ[F] TraceZero F :=
  rootDiagonalEquiv (longSL2DiagonalWeights a b)

set_option maxHeartbeats 1000000 in
theorem longSL2Diagonal_intertwine (a b : Fˣ) (u z : F) :
    longSL2Diagonal a b * longSL2Equiv u z =
      longSL2Equiv ((a:F)^2*u) ((b:F)^2*z) * longSL2Diagonal a b := by
  have ha : (a : F) ≠ 0 := Units.ne_zero a
  have hb : (b : F) ≠ 0 := Units.ne_zero b
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [longSL2Diagonal, rootDiagonalEquiv, rootDiagonalLinear,
        rootDiagonalFormula, longSL2DiagonalWeights,
        longSL2Equiv, longSL2Linear, longSL2Formula] <;> field_simp <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [longSL2Diagonal, rootDiagonalEquiv, rootDiagonalLinear,
        rootDiagonalFormula, longSL2DiagonalWeights,
        longSL2Equiv, longSL2Linear, longSL2Formula] <;> field_simp <;> ring

theorem longSL2Diagonal_conjugate (a b : Fˣ) (u z : F) :
    longSL2Diagonal a b * longSL2Equiv u z * (longSL2Diagonal a b)⁻¹ =
      longSL2Equiv ((a:F)^2*u) ((b:F)^2*z) := by
  rw [longSL2Diagonal_intertwine, mul_assoc, mul_inv_cancel, mul_one]

variable [Finite F]

set_option maxHeartbeats 800000 in
theorem torusWeight_longSL2 (m : ℕ) (a : Fˣ) (r : ShortRootLabel) :
    torusWeight m a a⁻¹ r = longSL2DiagonalWeights a (thetaUnits m a) r := by
  rw [torusWeight_eq_twisted m (thetaUnits m) a a⁻¹
    (thetaUnits_apply m a) (thetaUnits_apply m a⁻¹)]
  rcases r with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [twistedTorusWeight, torusCharacter, torusConstantExponents,
      torusThetaExponents, longSL2DiagonalWeights, map_inv,
      mul_assoc, mul_left_comm, mul_comm, pow_two]

theorem torusEquiv_longSL2 (m : ℕ) (a : Fˣ) :
    torusEquiv m a a⁻¹ = longSL2Diagonal a (thetaUnits m a) := by
  unfold torusEquiv longSL2Diagonal
  congr 1
  funext r
  exact torusWeight_longSL2 m a r

theorem longSL2Parameter_torus_conjugate (m : ℕ) (a : Fˣ) (u : F) :
    torusEquiv m a a⁻¹ * longSL2Equiv u (theta F m u) *
      (torusEquiv m a a⁻¹)⁻¹ =
    longSL2Equiv ((a:F)^2*u) (theta F m ((a:F)^2*u)) := by
  rw [torusEquiv_longSL2, longSL2Diagonal_conjugate]
  congr 1
  change (theta F m (a : F))^2 * theta F m u = theta F m ((a:F)^2*u)
  rw [map_mul, map_pow]

theorem longSL2Parameter_torus_one (m : ℕ) (a : Fˣ) :
    torusEquiv m a a⁻¹ * longRootEquiv * (torusEquiv m a a⁻¹)⁻¹ =
      longSL2Equiv ((a:F)^2) (theta F m ((a:F)^2)) := by
  simpa only [map_one, longSL2Equiv_one, mul_one] using
    longSL2Parameter_torus_conjugate m a 1

end Atlas.ReeF4
