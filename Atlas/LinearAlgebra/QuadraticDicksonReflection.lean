import Atlas.LinearAlgebra.QuadraticResidualOutside
import Mathlib.Data.ZMod.Basic

/-! # Intrinsic residual-rank parity under a quadratic reflection

These results apply in characteristic two as well as odd characteristic. They concern
actual residual spaces, independently of a reflection-generation theorem.
-/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (g : Q.IsometryEquiv Q)

/-- Residual-rank parity, the intrinsic candidate for the Dickson invariant. -/
def dicksonParity : ZMod 2 := (Module.finrank F (residual Q g) : ZMod 2)

omit [FiniteDimensional F V] in
@[simp] theorem dickson_reflectedIsometry_twice (a : V) (ha : Q a ≠ 0) :
    reflectedIsometry Q (reflectedIsometry Q g a ha) a ha = g := by
  apply DFunLike.ext
  intro x
  change reflectionLinear Q a ha (reflectionLinear Q a ha (g x)) = g x
  exact Module.involutive_reflection (reflectionFunctional_self Q a ha) (g x)

/-- An anisotropic reflecting vector outside the residual raises its dimension by one. -/
theorem reflected_residual_finrank_outside (hQ : Q.polarBilin.Nondegenerate)
    (a : V) (ha : Q a ≠ 0) (hout : a ∉ residual Q g) :
    Module.finrank F (residual Q (reflectedIsometry Q g a ha)) =
      Module.finrank F (residual Q g) + 1 := by
  have hin := outside_mem_reflected_residual Q g hQ a ha hout
  have h := reflected_residual_finrank Q (reflectedIsometry Q g a ha) ⟨a, hin⟩ ha
  change Module.finrank F
    (residual Q (reflectedIsometry Q (reflectedIsometry Q g a ha) a ha)) + 1 = _ at h
  rw [dickson_reflectedIsometry_twice] at h
  exact h.symm

/-- Left multiplication by an actual anisotropic reflection changes residual-rank
parity by one. No generation, target order or characteristic assumption is used. -/
theorem dicksonParity_reflection (hQ : Q.polarBilin.Nondegenerate)
    (a : V) (ha : Q a ≠ 0) :
    dicksonParity Q (reflectedIsometry Q g a ha) = dicksonParity Q g + 1 := by
  classical
  by_cases hin : a ∈ residual Q g
  · have h := reflected_residual_finrank Q g ⟨a, hin⟩ ha
    have hc := congrArg (fun n : ℕ => (n : ZMod 2)) h
    simp only [Nat.cast_add, Nat.cast_one] at hc
    unfold dicksonParity
    rw [← hc]
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    rw [add_assoc, htwo, add_zero]
  · have h := reflected_residual_finrank_outside Q g hQ a ha hin
    unfold dicksonParity
    rw [h, Nat.cast_add, Nat.cast_one]

end Atlas.Quadratic
