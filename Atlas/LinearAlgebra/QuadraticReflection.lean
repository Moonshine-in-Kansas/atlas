import Atlas.LinearAlgebra.QuadraticHyperbolic
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Tactic.FieldSimp

/-! # Quadratic reflections in arbitrary characteristic, with singular-vector transport -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def reflectionFunctional (a : V) : V →ₗ[F] F := (Q a)⁻¹ • Q.polarBilin.flip a

theorem reflectionFunctional_self (a : V) (ha : Q a ≠ 0) :
    reflectionFunctional Q a a = 2 := by
  change (Q a)⁻¹ * Q.polarBilin a a = 2
  rw [polar_self]
  field_simp

/-- The existing linear reflection, normalized using the quadratic value. -/
def reflectionLinear (a : V) (ha : Q a ≠ 0) : V ≃ₗ[F] V :=
  Module.reflection (reflectionFunctional_self Q a ha)

@[simp] theorem reflectionLinear_apply (a : V) (ha : Q a ≠ 0) (x : V) :
    reflectionLinear Q a ha x = x - ((Q a)⁻¹ * Q.polarBilin x a) • a :=
  Module.reflection_apply _ _

theorem reflection_preserves (a : V) (ha : Q a ≠ 0) (x : V) :
    Q (reflectionLinear Q a ha x) = Q x := by
  rw [reflectionLinear_apply,sub_eq_add_neg,← neg_smul,add_smul]
  field_simp
  ring

def reflectionIsometry (a : V) (ha : Q a ≠ 0) : Q.IsometryEquiv Q where
  __ := reflectionLinear Q a ha
  map_app' := reflection_preserves Q a ha

theorem sub_singular_value (u v : V) (hu : Q u=0) (hv : Q v=0) :
    Q (u-v) = -Q.polarBilin u v := by
  rw [sub_eq_add_neg,← neg_one_smul F v,add_smul,hu,hv]
  ring

/-- A single quadratic reflection transports two nonorthogonal singular vectors. -/
theorem reflection_transports (u v : V) (hu : Q u=0) (hv : Q v=0)
    (huv : Q.polarBilin u v ≠ 0) :
    ∃ g : Q.IsometryEquiv Q, g u=v := by
  have hq := sub_singular_value Q u v hu hv
  have ha : Q (u-v) ≠ 0 := by rw [hq]; exact neg_ne_zero.mpr huv
  refine ⟨reflectionIsometry Q (u-v) ha, ?_⟩
  change reflectionLinear Q (u-v) ha u=v
  have hp : Q.polarBilin u (u-v) = -Q.polarBilin u v := by
    rw [map_sub,polar_self,hu,mul_zero,zero_sub]
  rw [reflectionLinear_apply,hp,hq,inv_mul_cancel₀ (neg_ne_zero.mpr huv),one_smul]
  abel

end Atlas.Quadratic
