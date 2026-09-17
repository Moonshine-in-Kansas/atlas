import Atlas.LinearGroups.Orthogonal.ProjectiveElementary
import Atlas.LinearGroups.Orthogonal.CenterStandard
import Atlas.LinearGroups.Orthogonal.IntrinsicStandard
import Atlas.LinearGroups.Orthogonal.PerfectStable

/-! # The actual odd B scalar quotient: order, perfectness and noncommutativity -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

def projectiveElementaryBEquiv (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ProjectiveElementary (formB (n+2) F) ≃* elementarySubgroup (formB (n+2) F) :=
  (QuotientGroup.quotientMulEquivOfEq
    ((elementaryScalarSubgroup_eq_center _ (wittTwoFrameB n) (polarB_nondegenerate h2)).trans
      (elementaryB_center_eq_bot n h2))).trans QuotientGroup.quotientBot

theorem projectiveElementaryB_noncommutative (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ¬ IsMulCommutative (ProjectiveElementary (formB (n+2) F)) := by
  intro h
  exact elementaryB_noncommutative n h2
    (Function.Surjective.isMulCommutative (projectiveElementaryBEquiv n h2).surjective h)

variable [Finite F]

/-- This comparison identifies the counted scalar quotient with the actual intrinsic kernel. -/
def projectiveBKernelEquiv (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ProjectiveElementary (formB (n+2) F) ≃* oddSpinorKernelB (n+2) h2 :=
  (projectiveElementaryBEquiv n h2).trans (elementaryB_kernelEquiv n h2)

theorem card_projectiveElementaryB (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (ProjectiveElementary (formB (n+2) F)) =
      (Nat.card F ^ ((n+2)*(n+2)) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1)) / 2 := by
  rw [Nat.card_congr (projectiveElementaryBEquiv n h2).toEquiv]
  exact card_elementaryB n h2

theorem card_projectiveElementaryB_mul_two (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (ProjectiveElementary (formB (n+2) F)) * 2 =
      Nat.card F ^ ((n+2)*(n+2)) *
        ∏ i ∈ Finset.range (n+2), (Nat.card F ^ (2*(i+1))-1) := by
  rw [Nat.card_congr (projectiveBKernelEquiv n h2).toEquiv]
  have h := card_specialSpinorKernel_mul_two (formB (n+2) F) (polarB_nondegenerate h2) h2
    (fun c _ => formB_represents (n+1) c)
  change Nat.card (oddSpinorKernelB (n+2) h2) * 2 = Nat.card (SO_B (n+2) F) at h
  rw [card_specialB (n+2)] at h
  exact h

theorem projectiveElementaryB_perfect_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Group.IsPerfect (ProjectiveElementary (formB (n+3) F)) := by
  letI := elementaryB_perfect_stable n h2
  exact projectiveElementary_perfect _

theorem projectiveElementaryB_perfect_of_card_gt_three (n : ℕ) (h2 : (2 : F) ≠ 0)
    (hq : 3 < Nat.card F) : Group.IsPerfect (ProjectiveElementary (formB (n+2) F)) := by
  letI := elementaryB_perfect_of_card_gt_three n h2 hq
  exact projectiveElementary_perfect _
end Atlas.Orthogonal
