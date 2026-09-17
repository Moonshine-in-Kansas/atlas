import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

namespace Atlas.Algebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The square of an actual rank-one endomorphism, with no spectral hypothesis. -/
theorem rankOne_smulRight_square (f : V →ₗ[K] K) (x : V) :
    (f.smulRight x : Module.End K V) ^ 2 = f x • f.smulRight x := by
  ext y
  simp [pow_two, Module.End.mul_apply, LinearMap.smulRight_apply, smul_smul]
  congr 1
  ring

/-- Trace of a scalar rank-one perturbation squared. -/
theorem trace_one_add_rankOne_square [FiniteDimensional K V]
    (f : V →ₗ[K] K) (x : V) (a : K) :
    LinearMap.trace K V ((1 + a • f.smulRight x : Module.End K V) ^ 2) =
      (Module.finrank K V : K) + (2 * a + a ^ 2 * f x) * f x := by
  have he : (1 + a • f.smulRight x : Module.End K V) ^ 2 =
      1 + (2 * a + a ^ 2 * f x) • f.smulRight x := by
    ext y
    simp only [pow_two, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, map_add, map_smul,
      smul_add, smul_smul, smul_eq_mul]
    module
  rw [he, map_add, map_smul, LinearMap.trace_one, LinearMap.trace_smulRight, smul_eq_mul]

/-- The numerical trace used in the cubic root criterion, derived from rank one. -/
theorem trace_one_add_eleven_rankOne_square [CharZero K] [FiniteDimensional K V]
    (f : V →ₗ[K] K) (x : V) (hx : f x = 9) (hd : Module.finrank K V = 783) :
    LinearMap.trace K V ((1 + (11 : K) • f.smulRight x : Module.End K V) ^ 2) = 10782 := by
  rw [trace_one_add_rankOne_square, hx, hd]
  norm_num

end Atlas.Algebra
