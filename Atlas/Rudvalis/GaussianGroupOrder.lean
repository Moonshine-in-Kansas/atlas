import Atlas.Rudvalis.CanonicalFrameAction
import Atlas.Rudvalis.CanonicalFrameCount

namespace Atlas.Rudvalis

/-- The full Gaussian isometry group order is derived from intrinsic canonical frames and their full stabilizer. -/
theorem full_gaussian_order : Nat.card gaussianLatticeGroup=583704576000 := by
  rw [full_gaussian_order_eq_frames_mul,canonicalBases_card]

theorem generatedGaussianGroup_order : Nat.card generatedGaussianGroup=583704576000 := by
  rw [generatedGaussianGroup_eq_top]
  rw [Nat.card_congr (Subgroup.topEquiv.toEquiv : (⊤ : Subgroup gaussianLatticeGroup) ≃ gaussianLatticeGroup)]
  exact full_gaussian_order

end Atlas.Rudvalis
