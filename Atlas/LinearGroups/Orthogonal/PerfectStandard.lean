import Atlas.LinearGroups.Orthogonal.PerfectLarge
import Atlas.LinearGroups.Orthogonal.IntrinsicStandard

/-! # Perfectness of the actual odd B/D intrinsic kernels over fields of more than three elements -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem elementaryB_perfect_of_card_gt_three (n : ℕ) (h2 : (2 : F) ≠ 0)
    (hq : 3 < Nat.card F) : Group.IsPerfect (elementarySubgroup (formB (n+2) F)) :=
  elementary_perfect_of_card_gt_three _ (wittTwoFrameB n) (polarB_nondegenerate h2) h2 hq

theorem elementaryD_perfect_of_card_gt_three (n : ℕ) (h2 : (2 : F) ≠ 0)
    (hq : 3 < Nat.card F) : Group.IsPerfect (elementarySubgroup (formD (n+2) F)) :=
  elementary_perfect_of_card_gt_three _ (wittTwoFrameD n) polarD_nondegenerate h2 hq

theorem oddSpinorKernelB_perfect_of_card_gt_three (n : ℕ) (h2 : (2 : F) ≠ 0)
    (hq : 3 < Nat.card F) : Group.IsPerfect (oddSpinorKernelB (n+2) h2) := by
  letI := elementaryB_perfect_of_card_gt_three n h2 hq
  exact Group.IsPerfect.ofSurjective (f := (elementaryB_kernelEquiv n h2).toMonoidHom)
    (elementaryB_kernelEquiv n h2).surjective

theorem oddSpinorKernelD_perfect_of_card_gt_three (n : ℕ) (h2 : (2 : F) ≠ 0)
    (hq : 3 < Nat.card F) : Group.IsPerfect (oddSpinorKernelD (n+2) h2) := by
  letI := elementaryD_perfect_of_card_gt_three n h2 hq
  exact Group.IsPerfect.ofSurjective (f := (elementaryD_kernelEquiv n h2).toMonoidHom)
    (elementaryD_kernelEquiv n h2).surjective

end Atlas.Orthogonal
