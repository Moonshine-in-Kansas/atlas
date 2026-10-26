import Atlas.Rudvalis.KernelTranslations
import Atlas.Rudvalis.BinaryLiftAction
import Mathlib.GroupTheory.Index

/-! Full binary Hamming-weave automorphism group: exact kernel, quotient and order. -/
namespace Atlas.Rudvalis

noncomputable def binaryLinearMatrixEquiv :
    GL (Fin 3) Bit ≃* (E ≃ₗ[Bit] E) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv Bit E)

theorem binaryLinearGroup_order : Nat.card (E ≃ₗ[Bit] E) = 168 := by
  rw [← Nat.card_congr binaryLinearMatrixEquiv.toEquiv,Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ,ZMod.card]

theorem binaryBlockLinearHom_kernel_translations :
    binaryBlockLinearHom.ker = binaryTranslationSubgroup := by
  rw [binaryBlockLinearHom_ker,binaryBlockHom_kernel_translations]

theorem binaryBlockLinearHom_kernel_order : Nat.card binaryBlockLinearHom.ker = 512 := by
  rw [binaryBlockLinearHom_kernel_translations,binaryTranslationSubgroup_order]

theorem binaryPermutationGroup_order : Nat.card binaryPermutationGroup = 86016 := by
  rw [← binaryBlockLinearHom.ker.card_mul_index,Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr binaryBlockLinearHom_surjective]
  simp only [Subgroup.card_top,binaryBlockLinearHom_kernel_order,binaryLinearGroup_order]

/-- Exactness uses the actual translations and the actual induced Fano-linear action. -/
theorem binaryAutomorphism_exact :
    Function.Injective coordinateTranslationHom ∧
    binaryBlockLinearHom.ker = coordinateTranslationHom.range ∧
    Function.Surjective binaryBlockLinearHom :=
  ⟨coordinateTranslationHom_injective,binaryBlockLinearHom_kernel_translations,
    binaryBlockLinearHom_surjective⟩

end Atlas.Rudvalis
