import Atlas.LinearGroups.G2.RootGroups
import Mathlib.GroupTheory.Commutator.Basic

/-! A unit-constant long-root commutator, also valid over the binary field. -/
namespace Atlas.G2
open Explicit
open scoped commutatorElement
variable {F : Type*} [Field F]

theorem rootB_mul_rootE (s t : F) :
    rootB s * rootE t = rootA (s*t) * rootE t * rootB s := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [rootA,rootB,rootE,rootAEquiv,rootBEquiv,rootEEquiv,
      rootALinear,rootBLinear,rootELinear,rootAApply,rootBApply,rootEApply,
      Matrix.vecHead,Matrix.vecTail] <;> ring

theorem rootB_rootE_commutator (s t : F) : ⁅rootB s,rootE t⁆ = rootA (s*t) := by
  rw [commutatorElement_def,rootB_mul_rootE]
  simp [mul_assoc]

end Atlas.G2
