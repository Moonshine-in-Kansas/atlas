import Atlas.Algebra.SplitOctonion.BasisChecks
import Atlas.LinearGroups.G2.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Wilson's cyclic imaginary basis inside the installed split octonions over F₁₁.
No new octonion multiplication is introduced. -/
namespace Atlas.Janko1
instance primeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩
abbrev Field := ZMod 11

private theorem eleven_zero : (11 : Field) = 0 := by decide
private theorem twentyTwo_zero : (22 : Field) = 0 := by decide
private theorem thirtyThree_zero : (33 : Field) = 0 := by decide

/-- Scalar coordinate followed by the seven cyclic Wilson coordinates. -/
def wilsonEquiv : (Fin 8 → Field) ≃ₗ[Field] SplitOctonion.Carrier Field where
  toFun x := ![x 1 + 3*x 3 - x 7, x 2 + x 5 - 3*x 6,
    -x 4 + 3*x 5 + x 6, x 0 + x 3 + 3*x 7,
    x 0 - x 3 - 3*x 7, -x 4 - 3*x 5 - x 6,
    x 2 - x 5 + 3*x 6, x 1 - 3*x 3 + x 7]
  invFun x := ![6*x 3+6*x 4, 6*x 0+6*x 7, 6*x 1+6*x 6,
    4*x 0+5*x 3+6*x 4+7*x 7, 5*x 2+5*x 5,
    5*x 1+4*x 2+7*x 5+6*x 6, 7*x 1+5*x 2+6*x 5+4*x 6,
    6*x 0+4*x 3+7*x 4+5*x 7]
  left_inv x := by
    funext i
    fin_cases i <;> simp <;> apply sub_eq_zero.mp <;> ring_nf <;> simp [eleven_zero, twentyTwo_zero, thirtyThree_zero]
  right_inv x := by
    funext i
    fin_cases i <;> simp <;> apply sub_eq_zero.mp <;> ring_nf <;> simp [eleven_zero, twentyTwo_zero, thirtyThree_zero]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

def imaginaryVector (t : Fin 7) : SplitOctonion.Carrier Field :=
  ![![1,0,0,0,0,0,0,1], ![0,1,0,0,0,0,1,0],
    ![3,0,0,1,-1,0,0,-3], ![0,0,-1,0,0,-1,0,0],
    ![0,1,3,0,0,-3,-1,0], ![0,-3,1,0,0,-1,3,0],
    ![-1,0,0,3,-3,0,0,1]] t

theorem wilsonEquiv_unit : wilsonEquiv (Pi.single 0 1) = SplitOctonion.unit := by decide

theorem wilsonEquiv_imaginary : ∀ t : Fin 7,
    wilsonEquiv (Pi.single t.succ 1) = imaginaryVector t := by decide

theorem imaginary_square : ∀ t : Fin 7,
    SplitOctonion.mul (imaginaryVector t) (imaginaryVector t) = -SplitOctonion.unit := by decide

theorem imaginary_cyclic : ∀ t : Fin 7,
    SplitOctonion.mul (imaginaryVector t) (imaginaryVector (t+1)) = imaginaryVector (t+3) := by
  decide

theorem imaginary_skew : ∀ s t : Fin 7, s ≠ t →
    SplitOctonion.mul (imaginaryVector s) (imaginaryVector t) =
      -SplitOctonion.mul (imaginaryVector t) (imaginaryVector s) := by decide

theorem imaginary_trace : ∀ t : Fin 7, SplitOctonion.trace (imaginaryVector t) = 0 := by decide

theorem imaginary_norm : ∀ t : Fin 7, SplitOctonion.norm (imaginaryVector t) = 1 := by decide

theorem wilsonEquiv_trace (x : Fin 8 → Field) :
    SplitOctonion.trace (wilsonEquiv x) = 2*x 0 := by
  simp [wilsonEquiv, SplitOctonion.trace]
  ring

theorem wilsonEquiv_norm (x : Fin 8 → Field) :
    SplitOctonion.norm (wilsonEquiv x) = ∑ i, x i ^ 2 := by
  simp [wilsonEquiv, SplitOctonion.norm, Fin.sum_univ_succ]
  apply sub_eq_zero.mp
  ring_nf
  simp [eleven_zero, twentyTwo_zero, thirtyThree_zero]

noncomputable def wilsonBasis : Module.Basis (Fin 8) Field (SplitOctonion.Carrier Field) :=
  (Pi.basisFun Field (Fin 8)).map wilsonEquiv

end Atlas.Janko1
