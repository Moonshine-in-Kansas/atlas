import Atlas.LinearGroups.ReeG2.CompatibilityCharts
import Atlas.LinearGroups.ReeG2.CompatibilityReversal

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Only the affine origin has last coordinate zero. -/
theorem affine_last_zero_iff (m : ℕ) (hcard : Nat.card F = 3 ^ (2 * m + 1))
    (a b c : F) : affineVector m a b c 6 = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hz
    have hr := pointCompatibility_reverse m (affine_pointCompatibility m hcard a b c)
    have h0 : negativeReverse (affineVector m a b c) 0 = 0 := by
      simpa [negativeReverse] using congrArg Neg.neg hz
    obtain ⟨h1,h2,h3,h4,h5⟩ := compatible_zero_first m hr h0
    have ha : theta F m a = 0 := by
      simpa [negativeReverse, affineVector, rootMatrix_01] using h5
    have hb : theta F m b = 0 := by
      simpa [negativeReverse, affineVector, rootMatrix_02] using h4
    have hc : theta F m c = 0 := by
      simpa [negativeReverse, affineVector, rootMatrix_03, ha, hb] using h3
    exact ⟨(map_eq_zero (theta F m)).mp ha,
      (map_eq_zero (theta F m)).mp hb, (map_eq_zero (theta F m)).mp hc⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp [affineVector, rootMatrix_zero]

end Atlas.ReeG2
