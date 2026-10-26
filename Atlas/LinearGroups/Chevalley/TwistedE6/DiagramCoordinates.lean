import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.End

/-! The E6 diagram permutation and its integral coordinate action, separated
from the heavier existing norm-shell proofs. The original lattice numbering
has edges 01,12,23,34,25. -/
namespace Atlas.Chevalley.TwistedE6

/-- Reverse the long chain; fix its central node and the branch node. -/
def latticeNode : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 2, 1, 0, 5]
  invFun := ![4, 3, 2, 1, 0, 5]
  left_inv := by decide
  right_inv := by decide

theorem latticeNode_involutive : Function.Involutive latticeNode := by
  intro i
  fin_cases i <;> rfl

theorem latticeNode_ne_one : latticeNode ≠ 1 := by
  intro h
  have h0 := congrArg (fun e : Equiv.Perm (Fin 6) => e 0) h
  change (4 : Fin 6) = 0 at h0
  exact (by decide : (4 : Fin 6) ≠ 0) h0

variable (R : Type*) [CommRing R]

/-- Coordinate action of the diagram on the rank-six lattice. -/
def latticeDiagram : (Fin 6 → R) ≃ₗ[R] (Fin 6 → R) where
  toFun x i := x (latticeNode i)
  invFun x i := x (latticeNode i)
  left_inv x := funext fun i => congrArg x (latticeNode_involutive i)
  right_inv x := funext fun i => congrArg x (latticeNode_involutive i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem latticeDiagram_apply (x : Fin 6 → R) (i : Fin 6) :
    latticeDiagram R x i = x (latticeNode i) := rfl

theorem latticeDiagram_involutive : Function.Involutive (latticeDiagram R) := by
  intro x
  funext i
  exact congrArg x (latticeNode_involutive i)

theorem latticeDiagram_single (i : Fin 6) (t : R) :
    latticeDiagram R (Pi.single i t) = Pi.single (latticeNode i) t := by
  funext j
  have he : latticeNode j = i ↔ j = latticeNode i := latticeNode_involutive.eq_iff
  simp only [latticeDiagram_apply, Pi.single_apply, he]

end Atlas.Chevalley.TwistedE6
