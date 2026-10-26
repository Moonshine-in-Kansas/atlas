import Atlas.LinearGroups.ReeF4.RootSuzukiLeviGenerators
import Atlas.LinearGroups.ReeF4.RootGroupUnits

/-! The local Suzuki torus in the retained two-parameter Ree torus.
The parameter conversion is proved on units, using the actual finite-field
Tits identity; no false identity of free integer exponents is used. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Source Suzuki torus parameter t corresponds to Ree torus T(1,beta). -/
def suzukiLeviBeta (m : ℕ) (t : Fˣ) : Fˣ := (t * thetaUnits m t)⁻¹

def suzukiLeviTorusDiagonal (m : ℕ) (t : Fˣ) : Fin 4 → Fˣ :=
  ![t*thetaUnits m t,t,t⁻¹,(t*thetaUnits m t)⁻¹]

theorem suzukiLeviBeta_surjective {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Surjective (suzukiLeviBeta (F := F) m) := by
  intro b
  refine ⟨(thetaNormEquiv hcard).symm b⁻¹, ?_⟩
  change ((thetaNormEquiv hcard) ((thetaNormEquiv hcard).symm b⁻¹))⁻¹ = b
  rw [MulEquiv.apply_symm_apply, inv_inv]

set_option maxHeartbeats 1200000 in
theorem suzukiLeviTorusWeight_natural {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (t : Fˣ) (k i : Fin 4) :
    torusWeight m 1 (suzukiLeviBeta m t) (suzukiLeviBlockLabel k i) =
      suzukiLeviTorusDiagonal m t i := by
  rw [torusWeight_eq_twisted m (thetaUnits m) 1 (suzukiLeviBeta m t)
    (by simp) (thetaUnits_apply m _)]
  fin_cases k <;> fin_cases i <;>
    simp [twistedTorusWeight, torusCharacter, torusConstantExponents,
      torusThetaExponents, suzukiLeviBlockLabel, suzukiLeviBeta,
      suzukiLeviTorusDiagonal, thetaUnits_square hcard, pow_two, mul_assoc, mul_comm, mul_left_comm]

/-- The exterior basis positions occupied by nonzero roots. The middle two
positions are diagonal vectors, whose torus weight is one. -/
def suzukiLeviExteriorWeight (m : ℕ) (b : Fˣ) : Fin 6 → Fˣ :=
  ![torusWeight m 1 b (0,5),torusWeight m 1 b (0,4),1,1,
    torusWeight m 1 b (0,3),torusWeight m 1 b (0,2)]

set_option maxHeartbeats 1200000 in
theorem suzukiLeviTorusWeight_exterior {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (t : Fˣ) (i : Fin 6) :
    suzukiLeviExteriorWeight m (suzukiLeviBeta m t) i =
      suzukiLeviTorusDiagonal m t (suzukiLeviExteriorPair i).1 *
        suzukiLeviTorusDiagonal m t (suzukiLeviExteriorPair i).2 := by
  have ht (r : ShortRootLabel) := torusWeight_eq_twisted m (thetaUnits m) 1
    (suzukiLeviBeta m t) (by simp) (thetaUnits_apply m _) r
  unfold suzukiLeviExteriorWeight
  simp_rw [ht]
  fin_cases i <;>
    simp [suzukiLeviExteriorPair,
      twistedTorusWeight, torusCharacter, torusConstantExponents,
      torusThetaExponents, suzukiLeviBeta, suzukiLeviTorusDiagonal,
      thetaUnits_square hcard, pow_two, mul_assoc, mul_comm, mul_left_comm]

theorem suzukiLeviTorusDiagonal_h (m : ℕ) (t : Fˣ) :
    Matrix.diagonal (fun i => (suzukiLeviTorusDiagonal m t i : F)) =
      Atlas.SuzukiFamily.h m t := by
  unfold Atlas.SuzukiFamily.h
  congr 1
  funext i
  fin_cases i <;>
    simp [suzukiLeviTorusDiagonal, Atlas.SuzukiFamily.h, thetaUnits,
      -Atlas.SuzukiFamily.theta_apply, theta, _root_.map_mul, map_inv₀, mul_comm]


set_option maxHeartbeats 800000 in
theorem suzukiLeviExteriorMatrix_diagonal (d : Fin 4 → F) :
    suzukiLeviExteriorMatrix (Matrix.diagonal d) =
      Matrix.diagonal (fun i => d (suzukiLeviExteriorPair i).1 *
        d (suzukiLeviExteriorPair i).2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiLeviExteriorMatrix, suzukiLeviExteriorPair, Matrix.diagonal_apply]

theorem torusEquiv_suzukiBlock_h {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (t : Fˣ) (k : Fin 4) (w : TraceZero F) :
    suzukiLeviBlockProject k (torusEquiv m 1 (suzukiLeviBeta m t) w) =
      Atlas.SuzukiFamily.h m t *ᵥ suzukiLeviBlockProject k w := by
  rw [← suzukiLeviTorusDiagonal_h]
  funext i
  simp only [Matrix.mulVec_diagonal]
  change ((torusWeight (G := Fˣ) m 1 (suzukiLeviBeta m t)
      (suzukiLeviBlockLabel k i) : Fˣ) : F) *
    w.val.2 (suzukiLeviBlockLabel k i).1 (suzukiLeviBlockLabel k i).2 = _
  rw [suzukiLeviTorusWeight_natural hcard]
  rfl

theorem torusEquiv_suzukiExterior_weight (m : ℕ) (b : Fˣ) (w : TraceZero F) :
    suzukiLeviExteriorProject (torusEquiv m 1 b w) =
      Matrix.diagonal (fun i => (suzukiLeviExteriorWeight m b i : F)) *ᵥ
        suzukiLeviExteriorProject w := by
  funext i
  fin_cases i <;>
    simp [suzukiLeviExteriorProject, suzukiLeviCoordinates, suzukiLeviExteriorWeight,
      torusEquiv, rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula,
      Matrix.mulVec_diagonal]

theorem torusEquiv_suzukiExterior_h {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (t : Fˣ) (w : TraceZero F) :
    suzukiLeviExteriorProject (torusEquiv m 1 (suzukiLeviBeta m t) w) =
      suzukiLeviExteriorMatrix (Atlas.SuzukiFamily.h m t) *ᵥ
        suzukiLeviExteriorProject w := by
  rw [torusEquiv_suzukiExterior_weight, ← suzukiLeviTorusDiagonal_h,
    suzukiLeviExteriorMatrix_diagonal]
  congr 2
  funext i
  rw [suzukiLeviTorusWeight_exterior hcard, Units.val_mul]

theorem torusEquiv_suzukiFixed (m : ℕ) (b : Fˣ) (w : TraceZero F) :
    suzukiLeviFixedProject (torusEquiv m 1 b w) = suzukiLeviFixedProject w := by
  funext i
  fin_cases i <;>
    simp [suzukiLeviFixedProject, suzukiLeviCoordinates, torusEquiv,
      rootDiagonalEquiv, rootDiagonalLinear, rootDiagonalFormula,
      torusWeight, torusWeightExponents]

theorem suzukiLeviHom_torus {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (t : Fˣ) :
    suzukiLeviHom (Atlas.SuzukiFamily.torusElement m t) =
      torusEquiv m 1 (suzukiLeviBeta m t) := by
  apply LinearEquiv.ext
  intro w
  apply suzukiLeviCoordinatesEquiv.injective
  change suzukiLeviCoordinatesEquiv
      (suzukiLeviLinear (Atlas.SuzukiFamily.matrix (Atlas.SuzukiFamily.torusElement m t)) w) = _
  rw [suzukiLeviLinear_coordinates, Atlas.SuzukiFamily.matrix_torus]
  apply Prod.ext
  · funext k
    exact (torusEquiv_suzukiBlock_h hcard t k w).symm
  · apply Prod.ext
    · exact (torusEquiv_suzukiExterior_h hcard t w).symm
    · exact (torusEquiv_suzukiFixed m (suzukiLeviBeta m t) w).symm

end Atlas.ReeF4
