import Atlas.LinearGroups.Orthogonal.SpinorKernel
import Atlas.LinearGroups.Orthogonal.SpecialOrder

/-! # Exact orders of the actual odd-characteristic determinant-one spinor kernels

No elementary-generation or derived-subgroup identification is asserted here.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F]

theorem formD_represents (n : ℕ) (c : F) : ∃ a, formD (n+1) F a = c := by
  refine ⟨e 0 + c • f 0, ?_⟩
  rw [Atlas.Quadratic.add_smul, formD_e, formD_f, polarD_ef]
  ring

theorem formB_represents (n : ℕ) (c : F) : ∃ a, formB (n+1) F a = c := by
  obtain ⟨a, ha⟩ := formD_represents n c
  refine ⟨(a, 0), ?_⟩
  simp only [formB_apply, ha, zero_pow (by decide : 2 ≠ 0), add_zero]

abbrev oddSpinorKernelB (n : ℕ) (h2 : (2 : F) ≠ 0) :=
  ↥(specialSpinorKernel (formB n F) (polarB_nondegenerate h2) h2)

abbrev oddSpinorKernelD (n : ℕ) (h2 : (2 : F) ≠ 0) :=
  ↥(specialSpinorKernel (formD n F) polarD_nondegenerate h2)

variable [Finite F]

theorem card_oddSpinorKernelB (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (oddSpinorKernelB (n+1) h2) =
      (Nat.card F ^ ((n+1)*(n+1)) *
        ∏ i ∈ Finset.range (n+1), (Nat.card F ^ (2*(i+1))-1)) / 2 := by
  have h := card_specialSpinorKernel_mul_two (formB (n+1) F)
    (polarB_nondegenerate h2) h2 (fun c _ => formB_represents n c)
  change Nat.card (oddSpinorKernelB (n+1) h2) * 2 = Nat.card (SO_B (n+1) F) at h
  rw [card_specialB] at h
  rw [← h, Nat.mul_div_cancel _ (by decide : 0 < 2)]

theorem card_oddSpinorKernelD (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (oddSpinorKernelD (n+1) h2) =
      (Nat.card F ^ ((n+1)*n) * (Nat.card F ^ (n+1)-1) *
        ∏ i ∈ Finset.range n, (Nat.card F ^ (2*(i+1))-1)) / 2 := by
  have h := card_specialSpinorKernel_mul_two (formD (n+1) F)
    polarD_nondegenerate h2 (fun c _ => formD_represents n c)
  change Nat.card (oddSpinorKernelD (n+1) h2) * 2 = Nat.card (SO_DPlus (n+1) F) at h
  rw [card_specialD, if_neg h2, one_mul] at h
  rw [← h, Nat.mul_div_cancel _ (by decide : 0 < 2)]

end Atlas.Orthogonal
