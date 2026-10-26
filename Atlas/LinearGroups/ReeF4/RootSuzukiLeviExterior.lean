import Atlas.LinearGroups.ReeF4.RootSuzukiLeviRestrictions

/-! The six-dimensional exterior block in explicit ordered-pair coordinates.
The entries of `suzukiLeviExteriorMatrix` are the actual two-by-two minors,
not independently fitted coefficients. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert Matrix

/-- The ordered exterior basis 01,02,03,12,13,23. -/
def suzukiLeviExteriorPair (i : Fin 6) : Fin 4 × Fin 4 :=
  (![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]) i

variable {F : Type*} [CommRing F]

/-- The second compound matrix, in the explicit exterior-pair order. -/
def suzukiLeviExteriorMatrix (g : Matrix (Fin 4) (Fin 4) F) :
    Matrix (Fin 6) (Fin 6) F := fun i j =>
  g (suzukiLeviExteriorPair i).1 (suzukiLeviExteriorPair j).1 *
    g (suzukiLeviExteriorPair i).2 (suzukiLeviExteriorPair j).2 -
  g (suzukiLeviExteriorPair i).1 (suzukiLeviExteriorPair j).2 *
    g (suzukiLeviExteriorPair i).2 (suzukiLeviExteriorPair j).1

variable [CharP F 2]

def suzukiLeviExteriorProject : TraceZero F →ₗ[F] (Fin 6 → F) where
  toFun w := (suzukiLeviCoordinates w).2.1
  map_add' u v := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

def suzukiLeviFixedProject : TraceZero F →ₗ[F] (Fin 4 → F) where
  toFun w := (suzukiLeviCoordinates w).2.2
  map_add' u v := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

set_option maxHeartbeats 2400000 in
theorem shortRootPairLinear_suzukiExterior (τ : F →+* F) (a b : F)
    (w : TraceZero F) :
    suzukiLeviExteriorProject (shortRootPairLinear τ a b w) =
      suzukiLeviExteriorMatrix (suzukiLeviRootMatrix τ a b) *ᵥ
        suzukiLeviExteriorProject w := by
  funext i
  fin_cases i <;>
    simp [suzukiLeviExteriorProject, suzukiLeviCoordinates, shortRootPairLinear,
      Module.End.mul_apply, shortRootParameterLinear_val, shortRootCenterLinear_val,
      shortRootParameterFormula, shortRootCenterFormula, suzukiLeviRootMatrix,
      suzukiLeviExteriorMatrix, suzukiLeviExteriorPair,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, CharTwo.neg_eq] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> simp [CharTwo.two_eq_zero]

theorem shortRootPairLinear_suzukiFixed (τ : F →+* F) (a b : F)
    (w : TraceZero F) :
    suzukiLeviFixedProject (shortRootPairLinear τ a b w) =
      suzukiLeviFixedProject w := by
  funext i
  fin_cases i <;> rfl

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem shortRootPairEquiv_suzukiExterior (m : ℕ)
    (hcard : Nat.card K = 2^(2*m+1)) (a b : K) (w : TraceZero K) :
    suzukiLeviExteriorProject (shortRootPairEquiv m hcard a b w) =
      suzukiLeviExteriorMatrix (Atlas.SuzukiFamily.u m a (b+a*theta K m a)) *ᵥ
        suzukiLeviExteriorProject w := by
  rw [shortRootPairEquiv_apply, shortRootPairLinear_suzukiExterior,
    suzukiLeviRootMatrix_eq_suzuki m hcard]

set_option maxHeartbeats 1200000 in
theorem weylRho_suzukiExterior (w : TraceZero K) :
    suzukiLeviExteriorProject (weylRho w) =
      suzukiLeviExteriorMatrix (Atlas.SuzukiFamily.w : Matrix (Fin 4) (Fin 4) K) *ᵥ
        suzukiLeviExteriorProject w := by
  funext i
  fin_cases i <;>
    simp [suzukiLeviExteriorProject, suzukiLeviCoordinates, suzukiLeviExteriorMatrix,
      suzukiLeviExteriorPair, weylRho, weylTraceRestriction,
      weylRhoWilson, weylRhoCoordinates, wilsonTraceZeroEquiv, wilsonCoordinatesEquiv,
      Atlas.SuzukiFamily.w, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, CharTwo.neg_eq]

theorem weylRho_suzukiFixed (w : TraceZero K) :
    suzukiLeviFixedProject (weylRho w) = suzukiLeviFixedProject w := by
  funext i
  fin_cases i <;> rfl
end FiniteField

end Atlas.ReeF4
