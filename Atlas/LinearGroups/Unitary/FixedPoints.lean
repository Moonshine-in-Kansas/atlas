import Atlas.LinearGroups.Unitary.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Special unitary matrices as graph-field fixed points of SL

Only the special matrix group is identified with fixed points. No assertion is
made that fixed points commute with passage to the projective quotient.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

def adjointSpecial (hdeg : Module.finrank F K = 2)
    (g : Matrix.SpecialLinearGroup (Fin n) K) : Matrix.SpecialLinearGroup (Fin n) K := by
  letI := conjugationStarRing F K hdeg
  exact ⟨g.valᴴ, by rw [Matrix.det_conjTranspose, g.prop, star_one]⟩

theorem adjointSpecial_mul (hdeg : Module.finrank F K = 2)
    (g h : Matrix.SpecialLinearGroup (Fin n) K) :
    adjointSpecial hdeg (g * h) = adjointSpecial hdeg h * adjointSpecial hdeg g := by
  letI := conjugationStarRing F K hdeg
  apply Subtype.ext
  exact Matrix.conjTranspose_mul g.val h.val

@[simp] theorem adjointSpecial_one (hdeg : Module.finrank F K = 2) :
    adjointSpecial hdeg (1 : Matrix.SpecialLinearGroup (Fin n) K) = 1 := by
  letI := conjugationStarRing F K hdeg
  apply Subtype.ext
  exact Matrix.conjTranspose_one

@[simp] theorem adjointSpecial_twice (hdeg : Module.finrank F K = 2)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    adjointSpecial hdeg (adjointSpecial hdeg g) = g := by
  letI := conjugationStarRing F K hdeg
  apply Subtype.ext
  exact Matrix.conjTranspose_conjTranspose g.val

theorem adjointSpecial_inv (hdeg : Module.finrank F K = 2)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    adjointSpecial hdeg g⁻¹ = (adjointSpecial hdeg g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← adjointSpecial_mul, mul_inv_cancel, adjointSpecial_one]

/-- The actual graph-field automorphism g ↦ (conjugate-transpose g)⁻¹. -/
def graphFieldAutomorphism (hdeg : Module.finrank F K = 2) (n : ℕ) :
    MulAut (Matrix.SpecialLinearGroup (Fin n) K) where
  toFun g := adjointSpecial hdeg g⁻¹
  invFun g := adjointSpecial hdeg g⁻¹
  left_inv g := by simp only [adjointSpecial_inv, inv_inv, adjointSpecial_twice]
  right_inv g := by simp only [adjointSpecial_inv, inv_inv, adjointSpecial_twice]
  map_mul' g h := by rw [_root_.mul_inv_rev, adjointSpecial_mul]

theorem graphFieldAutomorphism_involutive (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Function.Involutive (graphFieldAutomorphism hdeg n) :=
  (graphFieldAutomorphism hdeg n).left_inv

theorem graphField_fixed_iff_unitary (hdeg : Module.finrank F K = 2)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    graphFieldAutomorphism hdeg n g = g ↔
      (letI := conjugationStarRing F K hdeg
       g.val ∈ Matrix.unitaryGroup (Fin n) K) := by
  letI := conjugationStarRing F K hdeg
  change adjointSpecial hdeg g⁻¹ = g ↔ _
  rw [adjointSpecial_inv, inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv,
    Matrix.mem_unitaryGroup_iff']
  exact Subtype.ext_iff

/-- Fixed points inside the actual special linear group. -/
def graphFieldFixed (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) K) :=
  (graphFieldAutomorphism hdeg n).toMonoidHom.eqLocus (MonoidHom.id _)

/-- The fixed subgroup is precisely the retained special unitary carrier,
with the same matrices and multiplication. -/
def specialUnitaryFixedEquiv (hdeg : Module.finrank F K = 2) (n : ℕ) :
    SU F K n hdeg ≃* graphFieldFixed hdeg n where
  toFun g := ⟨⟨g.val, g.prop.2⟩, (graphField_fixed_iff_unitary hdeg _).mpr g.prop.1⟩
  invFun g := ⟨g.val.val, (graphField_fixed_iff_unitary hdeg g.val).mp g.prop, g.val.prop⟩
  left_inv g := rfl
  right_inv g := rfl
  map_mul' g h := rfl

end Atlas.Unitary
