import Atlas.LinearGroups.Orthogonal.ProjectiveElementary
import Atlas.LinearGroups.Orthogonal.CenterOddDCongruence
import Atlas.LinearGroups.Orthogonal.PerfectStable

/-! # Exact order of the actual odd split-D scalar quotient -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem card_elementaryD_mul_two (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (elementarySubgroup (formD (n+2) F)) * 2 =
      Nat.card F ^ ((n+2)*(n+1)) * (Nat.card F ^ (n+2)-1) *
        ∏ i ∈ Finset.range (n+1), (Nat.card F ^ (2*(i+1))-1) := by
  rw [Nat.card_congr (elementaryD_kernelEquiv n h2).toEquiv]
  have h := card_specialSpinorKernel_mul_two (formD (n+2) F) polarD_nondegenerate h2
    (fun c _ => formD_represents (n+1) c)
  change Nat.card (oddSpinorKernelD (n+2) h2) * 2 = Nat.card (SO_DPlus (n+2) F) at h
  rw [card_specialD (n+1), if_neg h2, one_mul] at h
  exact h

/-- The denominator is forced by the proved intrinsic kernel and actual scalar center. -/
theorem card_projectiveElementaryD_mul_gcd (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (ProjectiveElementary (formD (n+2) F)) * Nat.gcd 4 (Nat.card F ^ (n+2)-1) =
      Nat.card F ^ ((n+2)*(n+1)) * (Nat.card F ^ (n+2)-1) *
        ∏ i ∈ Finset.range (n+1), (Nat.card F ^ (2*(i+1))-1) := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (elementaryScalarSubgroup (formD (n+2) F))
  change Nat.card (elementarySubgroup (formD (n+2) F)) =
    Nat.card (ProjectiveElementary (formD (n+2) F)) *
      Nat.card (elementaryScalarSubgroup (formD (n+2) F)) at hc
  rw [elementaryScalarSubgroup_eq_center _ (wittTwoFrameD n) polarD_nondegenerate] at hc
  rw [← card_elementaryD_center_mul_two n h2, ← mul_assoc, ← hc]
  exact card_elementaryD_mul_two n h2

theorem card_projectiveElementaryD (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (ProjectiveElementary (formD (n+2) F)) =
      (Nat.card F ^ ((n+2)*(n+1)) * (Nat.card F ^ (n+2)-1) *
        ∏ i ∈ Finset.range (n+1), (Nat.card F ^ (2*(i+1))-1)) /
      Nat.gcd 4 (Nat.card F ^ (n+2)-1) := by
  rw [← card_projectiveElementaryD_mul_gcd n h2,
    Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 4))]

theorem projectiveElementaryD_order_divisibility (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.gcd 4 (Nat.card F ^ (n+2)-1) ∣
      Nat.card F ^ ((n+2)*(n+1)) * (Nat.card F ^ (n+2)-1) *
        ∏ i ∈ Finset.range (n+1), (Nat.card F ^ (2*(i+1))-1) :=
  ⟨Nat.card (ProjectiveElementary (formD (n+2) F)), by
    simpa only [mul_comm] using (card_projectiveElementaryD_mul_gcd n h2).symm⟩

theorem projectiveElementaryD_perfect_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Group.IsPerfect (ProjectiveElementary (formD (n+3) F)) := by
  letI := elementaryD_perfect_stable n h2
  exact projectiveElementary_perfect _
theorem projectiveElementaryD_nontrivial (n : ℕ) :
    Nontrivial (ProjectiveElementary (formD (n+2) F)) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  have hk (g : elementarySubgroup (formD (n+2) F)) :
      g ∈ elementaryScalarSubgroup (formD (n+2) F) := by
    rw [← projectiveElementaryMap_kernel]
    exact @Subsingleton.elim _ hs (projectiveElementaryMap _ g) 1
  have hc : Subgroup.center (elementarySubgroup (formD (n+2) F)) = ⊤ := by
    apply top_unique
    intro g _
    exact elementaryScalarSubgroup_le_center _ (hk g)
  exact elementaryD_noncommutative n (Subgroup.center_eq_top_iff.mp hc)

theorem projectiveElementaryD_noncommutative_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ¬ IsMulCommutative (ProjectiveElementary (formD (n+3) F)) := by
  letI := projectiveElementaryD_nontrivial (F := F) (n+1)
  letI := projectiveElementaryD_perfect_stable n h2
  exact Group.IsPerfect.not_isMulCommutative _
end Atlas.Orthogonal

