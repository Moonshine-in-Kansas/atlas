import Atlas.LinearGroups.Unitary.Center
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-! # Faithful projective linear realization of the actual PSU quotient -/
noncomputable section
namespace Atlas.Unitary
open scoped MatrixGroups
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- The actual special unitary matrices regarded as invertible matrices. -/
def specialToGL (hdeg : Module.finrank F K = 2) : SU F K n hdeg →* GL (Fin n) K := by
  let := conjugationStarRing F K hdeg
  exact Unitary.toUnits.comp (specialInclusion hdeg)

def specialToPGL (hdeg : Module.finrank F K = 2) : SU F K n hdeg →* PGL(n, K) :=
  Matrix.ProjGenLinGroup.mk.comp (specialToGL hdeg)

theorem specialToPGL_kernel (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    (specialToPGL hdeg (n := n)).ker = Subgroup.center (SU F K n hdeg) := by
  ext g
  change Matrix.ProjGenLinGroup.mk (specialToGL hdeg g) = 1 ↔ _
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨a, ha⟩
    have hm : g.val = Matrix.diagonal (fun _ => (a : K)) :=
      (congrArg Units.val ha).symm
    obtain ⟨b, hb⟩ := scalar_matrix_parameter hdeg hn g a hm
    rw [← hb]
    exact scalarSpecial_mem_center F K hdeg n b
  · intro hg
    obtain ⟨a, ha⟩ := scalarCenterHom_surjective hdeg hn ⟨g, hg⟩
    have he : scalarSpecial F K hdeg a = g := congrArg Subtype.val ha
    subst g
    exact ⟨a.val.val, Units.ext rfl⟩

/-- The actual-center quotient embeds faithfully in the ambient PGL over K. -/
def projectiveEmbedding (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    PSU F K n hdeg →* PGL(n, K) :=
  QuotientGroup.lift _ (specialToPGL hdeg) (le_of_eq (specialToPGL_kernel hdeg hn).symm)

theorem projectiveEmbedding_injective (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    Function.Injective (projectiveEmbedding hdeg hn) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (specialToPGL_kernel hdeg hn).symm

@[simp] theorem projectiveEmbedding_mk (hdeg : Module.finrank F K = 2) (hn : 0 < n)
    (g : SU F K n hdeg) :
    projectiveEmbedding hdeg hn (QuotientGroup.mk g) = specialToPGL hdeg g := rfl
end Atlas.Unitary
