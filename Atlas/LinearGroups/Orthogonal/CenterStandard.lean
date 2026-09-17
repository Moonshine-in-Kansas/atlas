import Atlas.LinearGroups.Orthogonal.Center
import Atlas.LinearGroups.Orthogonal.WittTwoStandard
import Atlas.LinearGroups.Orthogonal.SingularCount

/-! # Actual centers and noncommutativity for standard elementary B/D models -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem elementaryB_noncommutative (n : ℕ) (h2 : (2 : F) ≠ 0) :
    ¬ IsMulCommutative (elementarySubgroup (formB (n+2) F)) :=
  elementary_noncommutative_of_frame _ (wittTwoFrameB n) (polarB_nondegenerate h2)

theorem elementaryD_noncommutative (n : ℕ) :
    ¬ IsMulCommutative (elementarySubgroup (formD (n+2) F)) :=
  elementary_noncommutative_of_frame _ (wittTwoFrameD n) polarD_nondegenerate

theorem elementaryD_center_scalar (n : ℕ) (z : elementarySubgroup (formD (n+2) F)) :
    z ∈ Subgroup.center (elementarySubgroup (formD (n+2) F)) ↔
      ∃ c : F, c^2 = 1 ∧ ∀ x, z.val.val x = c • x :=
  mem_elementary_center_iff_scalar _ (wittTwoFrameD n) polarD_nondegenerate z

/-- Odd-dimensional determinant one removes the possible negative scalar. -/
theorem elementaryB_center_eq_bot (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Subgroup.center (elementarySubgroup (formB (n+2) F)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨c, hc, hscalar⟩ := (mem_elementary_center_iff_scalar _ (wittTwoFrameB n)
    (polarB_nondegenerate h2) z).mp hz
  have hd : z.val.val.det = 1 := elementary_le_special _ z.prop
  have hm : z.val.val.toLinearMap = c • LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact hscalar x
  have hd' := congrArg Units.val hd
  rw [LinearEquiv.coe_det, hm, LinearMap.det_smul, LinearMap.det_id,
    mul_one, vectorB_finrank] at hd'
  have hc1 : c = 1 := by
    have hp : c^(2*(n+2)+1) = c := by
      rw [pow_add, pow_mul, hc, one_pow, one_mul, pow_one]
    exact hp.symm.trans hd'
  change z = 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change z.val.val x = x
  rw [hscalar, hc1, one_smul]

/-- In characteristic two the only possible scalar isometry is the identity. -/
theorem elementaryD_center_eq_bot_of_two_eq_zero (n : ℕ) (h2 : (2 : F) = 0) :
    Subgroup.center (elementarySubgroup (formD (n+2) F)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨c, hc, hscalar⟩ := (elementaryD_center_scalar n z).mp hz
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc with h | h
    · exact h
    · have hs : (-1 : F) = 1 := by linear_combination -h2
      exact h.trans hs
  change z = 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change z.val.val x = x
  rw [hscalar, hc1, one_smul]
end Atlas.Orthogonal
