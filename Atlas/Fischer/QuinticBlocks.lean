import Atlas.Fischer.QuinticCocodeSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- One term of the actual weighted contraction, with the two conjugations
retained in `coordinateQuinticCubicProduct`. -/
def coordinateQuinticTerm (i j k a b c p q r : CoordinateIndex) : Scalar :=
  inverseCoordinateMetric i * inverseCoordinateMetric j * inverseCoordinateMetric k *
    inverseCoordinateMetric a * inverseCoordinateMetric b * inverseCoordinateMetric c *
      coordinateQuinticCubicProduct i j k a b c p q r

theorem coordinateQuintic_eq_sum_term (p q r : CoordinateIndex) :
    coordinateQuintic p q r = ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      coordinateQuinticTerm i j k a b c p q r := by
  unfold coordinateQuintic coordinateQuinticTerm coordinateQuinticCubicProduct
  congr 12 <;> ring

/-- The ordered UWW internal pattern with its point edge in the first position. -/
def quinticPointUWW (p q r : Omega) : Scalar :=
  ∑ i : Omega, ∑ j : Octad, ∑ k : Octad, ∑ a : Omega, ∑ b : Octad, ∑ c : Octad,
    coordinateQuinticTerm (.inl i) (.inr j) (.inr k) (.inl a) (.inr b) (.inr c)
      (.inl p) (.inl q) (.inl r)

end Atlas.Fischer
