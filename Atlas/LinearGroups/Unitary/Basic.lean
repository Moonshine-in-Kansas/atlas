import Atlas.FieldTheory.FiniteQuadraticExtension
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-! # Actual finite unitary matrices for a quadratic extension

The carriers reuse mathlib's unitary and special unitary matrix groups. The star
structure is passed explicitly; no global star instance is installed on a field.
-/
noncomputable section
namespace Atlas.Unitary
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The canonical Hermitian star structure, used locally and explicitly. -/
@[instance_reducible] def conjugationStarRing (hdeg : Module.finrank F K = 2) : StarRing K where
  star := Atlas.FiniteQuadratic.conjugation F K
  star_involutive := Atlas.FiniteQuadratic.conjugation_involutive hdeg
  star_mul x y := by simp only [map_mul, mul_comm]
  star_add := map_add _

/-- The retained standard-coordinate unitary matrix carrier. -/
abbrev U (n : ℕ) (hdeg : Module.finrank F K = 2) :=
  letI := conjugationStarRing F K hdeg
  ↥(Matrix.unitaryGroup (Fin n) K)

/-- Determinant-one elements of the retained unitary matrix group. -/
abbrev SU (n : ℕ) (hdeg : Module.finrank F K = 2) :=
  letI := conjugationStarRing F K hdeg
  ↥(Matrix.specialUnitaryGroup (Fin n) K)

instance group_u (n : ℕ) (hdeg : Module.finrank F K = 2) : Group (U F K n hdeg) := by
  dsimp [U]
  infer_instance

instance group_su (n : ℕ) (hdeg : Module.finrank F K = 2) : Group (SU F K n hdeg) := by
  dsimp [SU]
  infer_instance

/-- The quotient by the actual center; scalar identification is a later theorem. -/
abbrev PSU (n : ℕ) (hdeg : Module.finrank F K = 2) :=
  SU F K n hdeg ⧸ Subgroup.center (SU F K n hdeg)

instance finite_u (n : ℕ) (hdeg : Module.finrank F K = 2) : Finite (U F K n hdeg) :=
  inferInstance
instance finite_su (n : ℕ) (hdeg : Module.finrank F K = 2) : Finite (SU F K n hdeg) :=
  inferInstance
instance finite_psu (n : ℕ) (hdeg : Module.finrank F K = 2) : Finite (PSU F K n hdeg) :=
  inferInstance

def projection (n : ℕ) (hdeg : Module.finrank F K = 2) :
    SU F K n hdeg →* PSU F K n hdeg := QuotientGroup.mk' _

theorem projection_surjective (n : ℕ) (hdeg : Module.finrank F K = 2) :
    Function.Surjective (projection F K n hdeg) := QuotientGroup.mk'_surjective _

theorem projection_kernel (n : ℕ) (hdeg : Module.finrank F K = 2) :
    (projection F K n hdeg).ker = Subgroup.center (SU F K n hdeg) :=
  QuotientGroup.ker_mk' _

/-- The mathematical order factor, with subtraction only in the even case. -/
def orderFactor (q i : ℕ) : ℕ := if Even i then q ^ i - 1 else q ^ i + 1

/-- Public positive simplicity parameters, independently of any group property. -/
def Good (n q : ℕ) : Prop :=
  2 ≤ n ∧ (n, q) ≠ (2, 2) ∧ (n, q) ≠ (2, 3) ∧ (n, q) ≠ (3, 2)
end Atlas.Unitary
