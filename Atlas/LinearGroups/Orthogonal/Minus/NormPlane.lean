import Atlas.FieldTheory.FiniteQuadraticCounts
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! The genuine anisotropic norm plane of a quadratic finite-field extension.
Its unhalved polar form is nondegenerate, including in characteristic two. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

private theorem norm_polar_formula (hdeg : Module.finrank F K = 2) (x y : K) :
    QuadraticMap.polar (norm F K) x y = trace F K (x * conjugation F K y) := by
  apply (algebraMap F K).injective
  simp only [QuadraticMap.polar, map_sub, norm_formula hdeg, trace_formula hdeg,
    map_add, map_mul, conjugation_conjugation hdeg]
  ring

/-- The field norm as a genuine quadratic form on the two-dimensional F-space K. -/
def normForm (hdeg : Module.finrank F K = 2) : QuadraticForm F K :=
  QuadraticMap.ofPolar (norm F K) (by
    intro r x
    apply (algebraMap F K).injective
    simp only [Algebra.smul_def, map_mul, norm_formula hdeg,
      conjugation_base, Algebra.algebraMap_self_apply]) (by
    intro x x' y
    simp only [norm_polar_formula hdeg, add_mul, map_add]) (by
    intro r x y
    simp only [norm_polar_formula hdeg, smul_mul_assoc, map_smul])

@[simp] theorem normForm_apply (hdeg : Module.finrank F K = 2) (x : K) :
    normForm hdeg x = norm F K x := rfl

/-- The unhalved polar convention is valid uniformly in every characteristic. -/
theorem normForm_polar (hdeg : Module.finrank F K = 2) (x y : K) :
    (normForm hdeg).polarBilin x y = trace F K (x * conjugation F K y) :=
  norm_polar_formula hdeg x y

@[simp] theorem normForm_eq_zero_iff (hdeg : Module.finrank F K = 2) (x : K) :
    normForm hdeg x = 0 ↔ x = 0 := norm_zero_iff hdeg x

theorem normForm_anisotropic (hdeg : Module.finrank F K = 2) :
    (normForm hdeg).Anisotropic := fun x hx => (normForm_eq_zero_iff hdeg x).mp hx

/-- Nonzero vectors have a polar partner of pairing one, using trace surjectivity. -/
theorem normForm_exists_polar_one (hdeg : Module.finrank F K = 2) (x : K)
    (hx : x ≠ 0) : ∃ y : K, (normForm hdeg).polarBilin x y = 1 := by
  obtain ⟨t,ht⟩ := trace_surjective F K 1
  refine ⟨conjugation F K (x⁻¹*t), ?_⟩
  rw [normForm_polar, conjugation_conjugation hdeg, ← mul_assoc, mul_inv_cancel₀ hx,
    one_mul, ht]

/-- Regularity of the norm plane does not use an invertibility hypothesis on two. -/
theorem normForm_polar_nondegenerate (hdeg : Module.finrank F K = 2) :
    (normForm hdeg).polarBilin.Nondegenerate := by
  have hleft : ∀ x : K, (∀ y, (normForm hdeg).polarBilin x y = 0) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨y,hy⟩ := normForm_exists_polar_one hdeg x hne
    exact zero_ne_one ((hx y).symm.trans hy)
  refine ⟨hleft, ?_⟩
  intro y hy
  apply hleft y
  intro x
  exact (QuadraticMap.polar_comm (normForm hdeg) y x).trans (hy x)

theorem normPlane_finrank (hdeg : Module.finrank F K = 2) : Module.finrank F K = 2 := hdeg
end Atlas.Orthogonal.Minus
