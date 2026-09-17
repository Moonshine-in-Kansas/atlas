import Atlas.LinearGroups.Orthogonal.B1ConjugationComparison
import Atlas.LinearGroups.ProjectiveSpecialLinear
import Atlas.LinearGroups.Orthogonal.SpinorStandard
import Atlas.LinearGroups.Orthogonal.SiegelSpinor
import Atlas.Algebra.FiniteFieldSignSquares
import Atlas.GroupTheory.DoubleTransitiveCenter
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! # Rank-one B structural center and intrinsic-kernel interfaces -/
noncomputable section
namespace Atlas.Orthogonal
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F] [Finite F]

/-- The actual PSL2 center is trivial, including the fields of two and three elements.
The proof uses its faithful doubly transitive action, not simplicity. -/
theorem psl_two_center_eq_bot :
    Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = ⊥ := by
  apply Atlas.center_eq_bot_of_two_transitive (X := ℙ F (Fin 2 → F))
  rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp)]
  have h := Finite.one_lt_card (α := F)
  omega

/-- The elementary quadratic B1 carrier has no nontrivial center in any finite characteristic. -/
theorem elementaryB_one_center_eq_bot :
    Subgroup.center (elementarySubgroup (formB 1 F)) = ⊥ := by
  let e := B1Conjugation.elementaryEquivPSL (F := F)
  apply bot_unique
  intro g hg
  have hm : e g ∈ Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨g,hg,rfl⟩
  rw [psl_two_center_eq_bot, Subgroup.mem_bot] at hm
  exact e.injective (hm.trans e.map_one.symm)

/-- The rank-one elementary and independently counted intrinsic kernels have equal orders. -/
theorem card_elementaryB_one_eq_oddKernel (h2 : (2 : F) ≠ 0) :
    Nat.card (elementarySubgroup (formB 1 F)) = Nat.card (oddSpinorKernelB 1 h2) := by
  rw [Nat.card_congr B1Conjugation.elementaryEquivPSL.toEquiv,
    Atlas.card_psl_factor 2, card_oddSpinorKernelB 0 h2]
  have ho := Atlas.odd_card_mod_two h2
  have hg : Nat.gcd 2 (Nat.card F - 1) = 2 := Nat.gcd_eq_left (by omega)
  norm_num [Finset.prod_Icc_succ_top, Finset.prod_range_succ, hg]

/-- The actual inclusion into the determinant-one intrinsic spinor kernel. -/
def elementaryB_one_to_oddKernel (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formB 1 F) →* oddSpinorKernelB 1 h2 where
  toFun g := ⟨⟨g.val, (elementary_le_special_spinor (formB 1 F)
    (polarB_nondegenerate h2) h2 g.prop).1⟩,
    (elementary_le_special_spinor (formB 1 F) (polarB_nondegenerate h2) h2 g.prop).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem elementaryB_one_to_oddKernel_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (elementaryB_one_to_oddKernel (F := F) h2) := by
  intro g h he
  exact Subtype.ext (congrArg (fun x : oddSpinorKernelB 1 h2 => x.val.val) he)

theorem elementaryB_one_to_oddKernel_surjective (h2 : (2 : F) ≠ 0) :
    Function.Surjective (elementaryB_one_to_oddKernel (F := F) h2) :=
  ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨elementaryB_one_to_oddKernel_injective h2, card_elementaryB_one_eq_oddKernel h2⟩).surjective

/-- Rank-one B satisfies the full intrinsic kernel condition, including the ternary field. -/
theorem elementaryB_one_eq_intrinsicKernel (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formB 1 F) = specialSubgroup (formB 1 F) ⊓
      (spinorNorm (formB 1 F) (polarB_nondegenerate h2) h2).ker := by
  apply le_antisymm (elementary_le_special_spinor _ _ h2)
  rintro g ⟨hg, hs⟩
  obtain ⟨a, ha⟩ := elementaryB_one_to_oddKernel_surjective h2 ⟨⟨g,hg⟩,hs⟩
  have he : a.val = g := congrArg (fun x : oddSpinorKernelB 1 h2 => x.val.val) ha
  rw [← he]
  exact a.prop

/-- The intrinsic equivalence retains the same underlying full orthogonal element. -/
def elementaryB_one_kernelEquiv (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formB 1 F) ≃* oddSpinorKernelB 1 h2 :=
  MulEquiv.ofBijective (elementaryB_one_to_oddKernel h2)
    ⟨elementaryB_one_to_oddKernel_injective h2, elementaryB_one_to_oddKernel_surjective h2⟩
end Atlas.Orthogonal

