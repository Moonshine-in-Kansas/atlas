import Atlas.LinearGroups.Orthogonal.ReflectionConjugation
import Atlas.LinearAlgebra.QuadraticSplit

/-! # Actual hyperbolic torus elements as products of two reflections -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
  (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

include he hf hef in
theorem hyperbolic_reflection_norm (c : F) : Q (e+c • f) = c := by
  rw [Atlas.Quadratic.add_smul, he, hf, hef]
  ring

def hyperbolicReflection (c : F) (hc : c ≠ 0) : isometrySubgroup Q :=
  reflectionElement Q (e+c • f) (ne_of_eq_of_ne (hyperbolic_reflection_norm Q e f he hf hef c) hc)

theorem hyperbolicReflection_e (c : F) (hc : c ≠ 0) :
    (hyperbolicReflection Q e f he hf hef c hc).val e = -c • f := by
  change reflectionLinear Q (e+c • f) (ne_of_eq_of_ne (hyperbolic_reflection_norm Q e f he hf hef c) hc) e = -c • f
  rw [reflectionLinear_apply, hyperbolic_reflection_norm Q e f he hf hef]
  have hee : Q.polarBilin e e = 0 := by rw [polar_self, he, mul_zero]
  simp only [map_add, map_smul, smul_eq_mul, hee, hef, mul_one, zero_add, inv_mul_cancel₀ hc,
    one_smul, neg_smul]
  abel

theorem hyperbolicReflection_f (c : F) (hc : c ≠ 0) :
    (hyperbolicReflection Q e f he hf hef c hc).val f = -c⁻¹ • e := by
  change reflectionLinear Q (e+c • f) (ne_of_eq_of_ne (hyperbolic_reflection_norm Q e f he hf hef c) hc) f = -c⁻¹ • e
  rw [reflectionLinear_apply, hyperbolic_reflection_norm Q e f he hf hef]
  have hff : Q.polarBilin f f = 0 := by rw [polar_self, hf, mul_zero]
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  simp only [map_add, map_smul, smul_eq_mul, hfe, hff, mul_zero, add_zero, mul_one,
    smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, neg_smul]
  abel

theorem hyperbolicReflection_perp (c : F) (hc : c ≠ 0) (w : complement Q e f) :
    (hyperbolicReflection Q e f he hf hef c hc).val w.val = w.val := by
  change reflectionLinear Q (e+c • f) (ne_of_eq_of_ne (hyperbolic_reflection_norm Q e f he hf hef c) hc) w.val = w.val
  rw [reflectionLinear_apply]
  have hwe : Q.polarBilin w.val e = 0 := w.prop.1
  have hwf : Q.polarBilin w.val f = 0 := w.prop.2
  simp only [map_add, map_smul, smul_eq_mul, hwe, hwf,
    mul_zero, add_zero, zero_smul, sub_zero]

def hyperbolicTorus (c : F) (hc : c ≠ 0) : isometrySubgroup Q :=
  hyperbolicReflection Q e f he hf hef 1 one_ne_zero * hyperbolicReflection Q e f he hf hef c hc

theorem hyperbolicTorus_e (c : F) (hc : c ≠ 0) :
    (hyperbolicTorus Q e f he hf hef c hc).val e = c • e := by
  change (hyperbolicReflection Q e f he hf hef 1 one_ne_zero).val
    ((hyperbolicReflection Q e f he hf hef c hc).val e) = c • e
  rw [hyperbolicReflection_e, map_smul, hyperbolicReflection_f]
  simp only [inv_one, neg_smul, one_smul, smul_neg, neg_neg]

theorem hyperbolicTorus_f (c : F) (hc : c ≠ 0) :
    (hyperbolicTorus Q e f he hf hef c hc).val f = c⁻¹ • f := by
  change (hyperbolicReflection Q e f he hf hef 1 one_ne_zero).val
    ((hyperbolicReflection Q e f he hf hef c hc).val f) = c⁻¹ • f
  rw [hyperbolicReflection_f, map_smul, hyperbolicReflection_e]
  simp only [neg_smul, one_smul, smul_neg, neg_neg]

theorem hyperbolicTorus_perp (c : F) (hc : c ≠ 0) (w : complement Q e f) :
    (hyperbolicTorus Q e f he hf hef c hc).val w.val = w.val := by
  change (hyperbolicReflection Q e f he hf hef 1 one_ne_zero).val
    ((hyperbolicReflection Q e f he hf hef c hc).val w.val) = w.val
  rw [hyperbolicReflection_perp, hyperbolicReflection_perp]

end Atlas.Orthogonal
