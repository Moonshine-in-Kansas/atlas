import Atlas.LinearGroups.Orthogonal.IntrinsicKernelIdentification
import Atlas.LinearGroups.Orthogonal.WittTwoStandard
import Atlas.LinearGroups.Orthogonal.SpinorStandard

/-! # Concrete odd-characteristic elementary, derived and intrinsic kernel identities -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem elementaryB_eq_intrinsicKernel (n : ℕ) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formB (n+2) F) = specialSubgroup (formB (n+2) F) ⊓
      (spinorNorm (formB (n+2) F) (polarB_nondegenerate h2) h2).ker :=
  elementary_eq_intrinsicKernel _ (wittTwoFrameB n) _ h2

theorem elementaryD_eq_intrinsicKernel (n : ℕ) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formD (n+2) F) = specialSubgroup (formD (n+2) F) ⊓
      (spinorNorm (formD (n+2) F) polarD_nondegenerate h2).ker :=
  elementary_eq_intrinsicKernel _ (wittTwoFrameD n) _ h2

theorem elementaryB_eq_commutator (n : ℕ) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formB (n+2) F) = commutator (O_B (n+2) F) :=
  elementary_eq_commutator _ (wittTwoFrameB n) (polarB_nondegenerate h2) h2

theorem elementaryD_eq_commutator (n : ℕ) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formD (n+2) F) = commutator (O_DPlus (n+2) F) :=
  elementary_eq_commutator _ (wittTwoFrameD n) polarD_nondegenerate h2

def elementaryB_kernelEquiv (n : ℕ) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formB (n+2) F) ≃* oddSpinorKernelB (n+2) h2 :=
  elementarySpecialSpinorEquiv _ (wittTwoFrameB n) (polarB_nondegenerate h2) h2

def elementaryD_kernelEquiv (n : ℕ) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formD (n+2) F) ≃* oddSpinorKernelD (n+2) h2 :=
  elementarySpecialSpinorEquiv _ (wittTwoFrameD n) polarD_nondegenerate h2

theorem card_elementaryB (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (elementarySubgroup (formB (n+2) F)) =
      (Nat.card F ^ ((n+2)*(n+2)) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1)) / 2 := by
  rw [Nat.card_congr (elementaryB_kernelEquiv n h2).toEquiv]
  exact card_oddSpinorKernelB (n+1) h2

theorem card_elementaryD (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (elementarySubgroup (formD (n+2) F)) =
      (Nat.card F ^ ((n+2)*(n+1)) * (Nat.card F ^ (n+2)-1) *
        ∏ i ∈ Finset.range (n+1), (Nat.card F ^ (2*(i+1))-1)) / 2 := by
  rw [Nat.card_congr (elementaryD_kernelEquiv n h2).toEquiv]
  exact card_oddSpinorKernelD (n+1) h2

end Atlas.Orthogonal
