import Atlas.LinearGroups.ReeF4.RootSuzukiLeviBlocks
import Atlas.LinearGroups.SuzukiFamily.Matrices

/-! The actual four-block restrictions of the root, Weyl and torus operators.
The root convention is the same parameter shear as the concrete root-group
isomorphism. No claim about the full local subgroup kernel is made here. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Matrix
variable {F : Type*} [CommRing F] [CharP F 2]

/-- Natural four-dimensional root matrix in the actual Ree parameters. -/
def suzukiLeviRootMatrix (τ : F →+* F) (a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,0,0; a,1,0,0; b,τ a,1,0; a^2*τ a+a*b+τ b,b+a*τ a,a,1]

set_option maxHeartbeats 1600000 in
theorem shortRootPairLinear_suzukiBlock (τ : F →+* F) (a b : F)
    (k : Fin 4) (w : TraceZero F) :
    suzukiLeviBlockProject k (shortRootPairLinear τ a b w) =
      suzukiLeviRootMatrix τ a b *ᵥ suzukiLeviBlockProject k w := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [suzukiLeviBlockProject, suzukiLeviBlockLabel, shortRootPairLinear,
      Module.End.mul_apply, shortRootParameterLinear_val, shortRootCenterLinear_val,
      shortRootParameterFormula, shortRootCenterFormula, suzukiLeviRootMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

set_option maxHeartbeats 800000 in
theorem suzukiLeviRootMatrix_eq_suzuki (m : ℕ)
    (hcard : Nat.card K = 2^(2*m+1)) (a b : K) :
    suzukiLeviRootMatrix (theta K m).toRingHom a b =
      Atlas.SuzukiFamily.u m a (b+a*theta K m a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiLeviRootMatrix, Atlas.SuzukiFamily.u, Atlas.SuzukiFamily.norm,
      -Atlas.SuzukiFamily.theta_apply, Atlas.SuzukiFamily.theta_square hcard,
      theta, _root_.map_add, _root_.map_mul] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> simp [CharTwo.two_eq_zero]

theorem shortRootPairEquiv_suzukiBlock (m : ℕ)
    (hcard : Nat.card K = 2^(2*m+1)) (a b : K) (k : Fin 4) (w : TraceZero K) :
    suzukiLeviBlockProject k (shortRootPairEquiv m hcard a b w) =
      Atlas.SuzukiFamily.u m a (b+a*theta K m a) *ᵥ suzukiLeviBlockProject k w := by
  rw [shortRootPairEquiv_apply, shortRootPairLinear_suzukiBlock,
    suzukiLeviRootMatrix_eq_suzuki m hcard]

set_option maxHeartbeats 800000 in
theorem weylRho_suzukiBlock (k : Fin 4) (w : TraceZero K) :
    suzukiLeviBlockProject k (weylRho w) =
      (Atlas.SuzukiFamily.w : Matrix (Fin 4) (Fin 4) K) *ᵥ suzukiLeviBlockProject k w := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [suzukiLeviBlockProject, suzukiLeviBlockLabel, weylRho, weylTraceRestriction,
      weylRhoWilson, weylRhoCoordinates, wilsonTraceZeroEquiv, wilsonCoordinatesEquiv,
      Atlas.SuzukiFamily.w, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end FiniteField

/-- Torus matrix before the field-twist change of its nonzero parameter. -/
def suzukiLeviTorusMatrix (m : ℕ) (b : Fˣ) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal ![(↑(b⁻¹) : F),
    ↑(b ^ ((1 : ℤ)-(2^(m+1) : ℕ))),
    ↑(b ^ (((2^(m+1) : ℕ) : ℤ)-1)), ↑b]

set_option maxHeartbeats 800000 in
theorem torusEquiv_suzukiBlock (m : ℕ) (b : Fˣ) (k : Fin 4) (w : TraceZero F) :
    suzukiLeviBlockProject k (torusEquiv m 1 b w) =
      suzukiLeviTorusMatrix m b *ᵥ suzukiLeviBlockProject k w := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [suzukiLeviBlockProject, suzukiLeviBlockLabel, torusEquiv, rootDiagonalEquiv,
      rootDiagonalLinear, rootDiagonalFormula, torusWeight, torusWeightExponents,
      suzukiLeviTorusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.diagonal_apply]

end Atlas.ReeF4
