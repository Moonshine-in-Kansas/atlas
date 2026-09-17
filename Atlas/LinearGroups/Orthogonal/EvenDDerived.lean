import Atlas.LinearGroups.Orthogonal.FullDicksonD
import Atlas.LinearGroups.Orthogonal.PerfectAllCharD
import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB
import Atlas.LinearGroups.Orthogonal.SimplicityAllCharD
import Mathlib.GroupTheory.Abelianization.Defs

/-! # The intrinsic derived and Dickson-kernel models of even split D

The derived-subgroup equality uses only the full Dickson character and proved
perfectness. Simplicity is transferred afterward through actual carrier maps.
-/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

/-- In characteristic two the actual elementary split-D subgroup is the derived
subgroup of the full orthogonal group. No simplicity theorem is used. -/
theorem elementaryD_eq_commutator_even (n : ℕ) :
    elementarySubgroup (formD (n + 3) F) = commutator (O_DPlus (n + 3) F) := by
  apply le_antisymm
  · letI := elementaryD_perfect_all_char (F := F) n
    rw [← Subgroup.commutator_eq_self (H := elementarySubgroup (formD (n + 3) F))]
    exact Subgroup.commutator_mono le_top le_top
  · rw [← fullDicksonD_kernel_elementary]
    exact Abelianization.commutator_subset_ker (fullDicksonD n)

/-- Equality of the two intrinsic full-group kernels. -/
theorem fullDicksonD_kernel_eq_commutator (n : ℕ) :
    (fullDicksonD (F := F) n).ker = commutator (O_DPlus (n + 3) F) := by
  rw [fullDicksonD_kernel_elementary,elementaryD_eq_commutator_even]

/-- Identity on ambient isometries identifies E with the actual full-character kernel. -/
def evenDElementaryKernelEquiv (n : ℕ) :
    elementarySubgroup (formD (n + 3) F) ≃* (fullDicksonD (F := F) n).ker :=
  MulEquiv.subgroupCongr (fullDicksonD_kernel_elementary n).symm

@[simp] theorem evenDElementaryKernelEquiv_coe (n : ℕ)
    (g : elementarySubgroup (formD (n + 3) F)) :
    (evenDElementaryKernelEquiv n g).val = g.val := rfl

/-- The scalar quotient identifies with the actual kernel because the scalar
subgroup is trivial in characteristic two. -/
def evenDProjectiveKernelEquiv (n : ℕ) :
    ProjectiveElementary (formD (n + 3) F) ≃* (fullDicksonD (F := F) n).ker :=
  (evenProjectiveElementaryEquiv _).trans (evenDElementaryKernelEquiv n)

/-- The projective comparison commutes with projection and the ambient lattice action. -/
theorem evenDProjectiveKernelEquiv_projection (n : ℕ)
    (g : elementarySubgroup (formD (n + 3) F)) :
    evenDProjectiveKernelEquiv n (projectiveElementaryMap _ g) =
      evenDElementaryKernelEquiv n g := rfl

theorem evenDProjectiveKernelEquiv_projection_coe (n : ℕ)
    (g : elementarySubgroup (formD (n + 3) F)) :
    (evenDProjectiveKernelEquiv n (projectiveElementaryMap _ g)).val = g.val := rfl

/-- The actual full Dickson kernel is perfect independently of simplicity. -/
theorem fullDicksonD_kernel_perfect (n : ℕ) :
    Group.IsPerfect (fullDicksonD (F := F) n).ker := by
  letI := elementaryD_perfect_all_char (F := F) n
  exact Group.IsPerfect.ofSurjective (f := (evenDElementaryKernelEquiv n).toMonoidHom)
    (evenDElementaryKernelEquiv n).surjective

/-- Simplicity of the actual full-group kernel, transferred from the same
projective quadratic model through the proved carrier equivalence. -/
theorem fullDicksonD_kernel_simple (n : ℕ) : IsSimpleGroup (fullDicksonD (F := F) n).ker := by
  letI := projectiveD_simple_all_char (F := F) n
  exact (evenDProjectiveKernelEquiv n).symm.isSimpleGroup

/-- Noncommutativity of the same intrinsic kernel. -/
theorem fullDicksonD_kernel_noncommutative (n : ℕ) :
    ¬ IsMulCommutative (fullDicksonD (F := F) n).ker := by
  letI := fullDicksonD_kernel_simple (F := F) n
  letI := fullDicksonD_kernel_perfect (F := F) n
  exact Group.IsPerfect.not_isMulCommutative _

end Atlas.Orthogonal
