import Atlas.Lattices.ConwayWales.FrameCode
import Atlas.Lattices.ConwayWales.CyclicFactors
import Mathlib.Algebra.Polynomial.AlgebraMap

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open Polynomial

/-- The actual cyclic block shift, restricted to the actual lattice code. -/
def frameShift : Module.End (ZMod 4) frameCodeModule where
  toFun c := ⟨shiftCoordinates 1 c.val, frameCode_shift 1 c.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem frameShift_pow_apply (n : ℕ) (c : frameCodeModule) (i : RealIndex) :
    ((frameShift ^ n) c).val i = c.val (i.1 - (n • (1 : Row)), i.2) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((frameShift ^ n) c).val (i.1-1,i.2) = _
    rw [ih]
    rw [succ_nsmul]
    have heq : i.1 - 1 - n • (1 : Row) = i.1 - (n • (1 : Row) + 1) := by abel
    exact congrArg (fun r => c.val (r,i.2)) heq

theorem frameShift_seventh : frameShift ^ 7 = 1 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext i
  rw [frameShift_pow_apply]
  change c.val (i.1 - (7 • (1 : Row)), i.2) = c.val i
  rw [show 7 • (1 : Row) = 0 by decide, sub_zero]

/-- Polynomial evaluation factors through t^7−1 on the given frame code. -/
def frameCodeCyclicAction : CyclicRing →+* Module.End (ZMod 4) frameCodeModule :=
  Ideal.Quotient.lift _ (Polynomial.aeval frameShift).toRingHom (by
    change Ideal.span {X^7-1} ≤ RingHom.ker (Polynomial.aeval frameShift).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change Polynomial.aeval frameShift (X^7-1) = 0
    simp only [map_sub, map_pow, aeval_X, map_one, frameShift_seventh, sub_self])

/-- The cyclic-ring scalar structure acts on the original frame code subtype. -/
scoped instance frameCodeCyclicModule : Module CyclicRing frameCodeModule :=
  Module.compHom frameCodeModule frameCodeCyclicAction

/-- The CRT product acts through the already constructed quotient-ring action. -/
def frameComponentAction :
    (CyclicComponent cyclicFactorZero ×
      (CyclicComponent cyclicFactorPlus × CyclicComponent cyclicFactorMinus)) →+*
      Module.End (ZMod 4) frameCodeModule :=
  frameCodeCyclicAction.comp cyclicCRT.symm.toRingHom

def frameProjectionZero := frameComponentAction (1,0,0)
def frameProjectionPlus := frameComponentAction (0,1,0)
def frameProjectionMinus := frameComponentAction (0,0,1)

theorem frameProjections_sum :
    frameProjectionZero + frameProjectionPlus + frameProjectionMinus = 1 := by
  rw [frameProjectionZero, frameProjectionPlus, frameProjectionMinus, ← map_add, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]
  exact frameComponentAction.map_one

theorem frameProjectionZero_sq : frameProjectionZero * frameProjectionZero = frameProjectionZero := by
  rw [frameProjectionZero, ← map_mul]
  congr 1 <;> ext <;> simp

theorem frameProjectionPlus_sq : frameProjectionPlus * frameProjectionPlus = frameProjectionPlus := by
  rw [frameProjectionPlus, ← map_mul]
  congr 1 <;> ext <;> simp

theorem frameProjectionMinus_sq : frameProjectionMinus * frameProjectionMinus = frameProjectionMinus := by
  rw [frameProjectionMinus, ← map_mul]
  congr 1 <;> ext <;> simp

theorem frameProjections_zero_plus : frameProjectionZero * frameProjectionPlus = 0 := by
  rw [frameProjectionZero, frameProjectionPlus, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul, mul_one, one_mul]
  exact frameComponentAction.map_zero

theorem frameProjections_zero_minus : frameProjectionZero * frameProjectionMinus = 0 := by
  rw [frameProjectionZero, frameProjectionMinus, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul, mul_one, one_mul]
  exact frameComponentAction.map_zero

theorem frameProjections_plus_minus : frameProjectionPlus * frameProjectionMinus = 0 := by
  rw [frameProjectionPlus, frameProjectionMinus, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul, mul_one, one_mul]
  exact frameComponentAction.map_zero

theorem frameProjections_plus_zero : frameProjectionPlus * frameProjectionZero = 0 := by
  rw [frameProjectionPlus, frameProjectionZero, ← map_mul, mul_comm, map_mul]
  exact frameProjections_zero_plus

theorem frameProjections_minus_zero : frameProjectionMinus * frameProjectionZero = 0 := by
  rw [frameProjectionMinus, frameProjectionZero, ← map_mul, mul_comm, map_mul]
  exact frameProjections_zero_minus

theorem frameProjections_minus_plus : frameProjectionMinus * frameProjectionPlus = 0 := by
  rw [frameProjectionMinus, frameProjectionPlus, ← map_mul, mul_comm, map_mul]
  exact frameProjections_plus_minus

/-- Every actual codeword is the sum of its three CRT projections. -/
theorem frameCode_decomposition (c : frameCodeModule) :
    frameProjectionZero c + frameProjectionPlus c + frameProjectionMinus c = c := by
  have h := congrArg (fun f : Module.End (ZMod 4) frameCodeModule => f c) frameProjections_sum
  exact h

/-- Independently selected CRT components combine to a codeword in the original code. -/
theorem frameCode_component_independence (x y z : frameCodeModule) :
    ∃ c : frameCodeModule,
      frameProjectionZero c = frameProjectionZero x ∧
      frameProjectionPlus c = frameProjectionPlus y ∧
      frameProjectionMinus c = frameProjectionMinus z := by
  refine ⟨frameProjectionZero x + frameProjectionPlus y + frameProjectionMinus z, ?_⟩
  simp only [map_add, ← Module.End.mul_apply, frameProjectionZero_sq,
    frameProjectionPlus_sq, frameProjectionMinus_sq, frameProjections_zero_plus,
    frameProjections_zero_minus, frameProjections_plus_minus, frameProjections_plus_zero,
    frameProjections_minus_zero, frameProjections_minus_plus, LinearMap.zero_apply,
    add_zero, zero_add, and_self]

end Atlas.ConwayWales


