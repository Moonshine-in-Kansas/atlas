import Atlas.Fischer.GolayCommonEigenspaces
import Atlas.Fischer.DuadComponentWeights

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Only weights zero, eight, sixteen and twenty-four occur as rational
coordinate characters of the actual 783-dimensional algebra. -/
theorem rationalCoordinateGolayWord_weights (p : RationalCoordinateIndex) :
    hammingNorm (rationalCoordinateGolayWord p).val = 0 ∨
    hammingNorm (rationalCoordinateGolayWord p).val = 8 ∨
    hammingNorm (rationalCoordinateGolayWord p).val = 16 ∨
    hammingNorm (rationalCoordinateGolayWord p).val = 24 := by
  obtain ⟨a,k⟩ := p
  cases a with
  | inl i =>
    by_cases hk : k=0
    · left
      simp [rationalCoordinateGolayWord,hk,hammingNorm]
    · right; right; right
      simpa [rationalCoordinateGolayWord,hk] using
        ((weight_twentyfour_iff golayOne.val).mpr rfl)
  | inr D =>
    by_cases hk : k=0
    · right; left
      simpa [rationalCoordinateGolayWord,hk] using octadWord_weight D
    · right; right; left
      have hw := complement_weight (octadWord D).val
      change hammingNorm (octadWord D+golayOne).val+hammingNorm (octadWord D).val=24 at hw
      rw [octadWord_weight] at hw
      simp only [rationalCoordinateGolayWord,if_neg hk]
      omega

/-- A dodecad character has no eigenspace in this actual coordinate algebra. -/
theorem golayCommonEigenvector_weight_twelve_zero (c : golay)
    (hc : hammingNorm c.val = 12) (x : Coordinates) (hx : GolayCommonEigenvector c x) : x = 0 := by
  apply rationalCoordinateEquiv.injective
  funext p
  simp only [map_zero,Pi.zero_apply]
  apply (golayCommonEigenvector_iff c x).mp hx p
  intro hp
  have hw := rationalCoordinateGolayWord_weights p
  rw [hp,hc] at hw
  omega

end Atlas.Fischer
