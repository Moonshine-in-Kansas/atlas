import Atlas.LinearGroups.Orthogonal.SpecialStandard
import Atlas.LinearAlgebra.QuadraticResidual

/-! # Hyperbolic exchanges and their residual lines in every characteristic

In characteristic two the determinant cannot detect this exchange, but its
residual space still has dimension one. -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include he hf hef in
theorem exchange_direction_value : Q (e-f) = -1 := by
  rw [sub_singular_value Q e f he hf, hef]

include he hf hef in
theorem exchange_direction_nonzero : Q (e-f) ≠ 0 := by
  rw [exchange_direction_value Q e f he hf hef]
  exact neg_ne_zero.mpr one_ne_zero

def hyperbolicExchange : Q.IsometryEquiv Q :=
  reflectionIsometry Q (e-f) (by rw [exchange_direction_value Q e f he hf hef]; exact neg_ne_zero.mpr one_ne_zero)

@[simp] theorem hyperbolicExchange_e : hyperbolicExchange Q e f he hf hef e = f := by
  change reflectionLinear Q (e-f) (exchange_direction_nonzero Q e f he hf hef) e = f
  rw [reflectionLinear_apply, exchange_direction_value Q e f he hf hef]
  have hp : Q.polarBilin e (e-f) = -1 := by
    rw [map_sub, polar_self, he, hef, mul_zero, zero_sub]
  rw [hp]
  simp

@[simp] theorem hyperbolicExchange_f : hyperbolicExchange Q e f he hf hef f = e := by
  change reflectionLinear Q (e-f) (exchange_direction_nonzero Q e f he hf hef) f = e
  rw [reflectionLinear_apply, exchange_direction_value Q e f he hf hef]
  have hp : Q.polarBilin f (e-f) = 1 := by
    rw [map_sub, polar_self, hf, polar_swap Q f e, hef, mul_zero, sub_zero]
  rw [hp]
  simp

theorem hyperbolicExchange_fixed (x : V) (hxe : Q.polarBilin x e = 0)
    (hxf : Q.polarBilin x f = 0) : hyperbolicExchange Q e f he hf hef x = x := by
  change reflectionLinear Q (e-f) (exchange_direction_nonzero Q e f he hf hef) x = x
  have hp : Q.polarBilin x (e-f) = 0 := by rw [map_sub, hxe, hxf, sub_self]
  rw [reflectionLinear_apply, hp, mul_zero, zero_smul, sub_zero]

theorem hyperbolicExchange_residual :
    residual Q (hyperbolicExchange Q e f he hf hef) = Submodule.span F {e-f} := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    change y - reflectionLinear Q (e-f) (exchange_direction_nonzero Q e f he hf hef) y ∈ _
    rw [reflectionLinear_apply, sub_sub_cancel]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro x (rfl : x = e-f)
    exact ⟨e, by simp⟩

theorem hyperbolicExchange_residual_finrank :
    Module.finrank F (residual Q (hyperbolicExchange Q e f he hf hef)) = 1 := by
  rw [hyperbolicExchange_residual]
  apply finrank_span_singleton
  intro h
  have hv := exchange_direction_value Q e f he hf hef
  rw [h, map_zero] at hv
  exact neg_ne_zero.mpr (one_ne_zero : (1:F) ≠ 0) hv.symm

variable {n : ℕ}
def splitDExchange (i : Fin n) : (formD n F).IsometryEquiv (formD n F) :=
  hyperbolicExchange _ (Atlas.Orthogonal.e i) (Atlas.Orthogonal.f i)
    (formD_e i) (formD_f i) (polarD_ef i)

theorem splitDExchange_residual_finrank (i : Fin n) :
    Module.finrank F (residual (formD n F) (splitDExchange (F:=F) i)) = 1 :=
  hyperbolicExchange_residual_finrank _ _ _ _ _ _

theorem hyperbolicExchange_ne_one : hyperbolicExchange Q e f he hf hef ≠
    QuadraticMap.IsometryEquiv.refl Q := by
  intro h
  have heq : e = f := by
    have hv := congrArg (fun g : Q.IsometryEquiv Q => g e) h
    change hyperbolicExchange Q e f he hf hef e = e at hv
    rw [hyperbolicExchange_e] at hv
    exact hv.symm
  have hz := exchange_direction_nonzero Q e f he hf hef
  rw [heq, sub_self, map_zero] at hz
  exact hz rfl

theorem splitDExchange_determinant (i : Fin n) :
    determinant (formD n F) ((isometryCarrierEquiv _).symm (splitDExchange (F:=F) i)) = -1 :=
  reflectionElement_determinant _ _ _

theorem splitDExchange_special [CharP F 2] (i : Fin n) :
    (isometryCarrierEquiv _).symm (splitDExchange (F:=F) i) ∈ specialSubgroup (formD n F) := by
  change determinant _ _ = 1
  rw [splitDExchange_determinant]
  apply Units.ext
  change (-1 : F) = 1
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination -h2

end Atlas.Orthogonal

