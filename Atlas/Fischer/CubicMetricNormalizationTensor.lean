import Atlas.Fischer.CubicMetricNormalization

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

/-- Cubic coefficients in the actual normalized complex coordinate basis. -/
def normalizedCoordinateCubic (i j k : CoordinateIndex) : ℂ :=
  cubicMetricScale i * cubicMetricScale j * cubicMetricScale k * scalarToComplex (coordinateCubic i j k)

/-- The exact source six-index contraction, now in orthonormal complex coordinates. -/
def normalizedCoordinateQuintic (p q r : CoordinateIndex) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
    star (normalizedCoordinateCubic i j k) * star (normalizedCoordinateCubic a b c) *
      normalizedCoordinateCubic a i p * normalizedCoordinateCubic b j q * normalizedCoordinateCubic c k r

/-- Every internal index contributes two normalization scales, hence one inverse metric. -/
theorem normalizedCoordinateQuintic_term (p q r i j k a b c : CoordinateIndex) :
    star (normalizedCoordinateCubic i j k) * star (normalizedCoordinateCubic a b c) *
      normalizedCoordinateCubic a i p * normalizedCoordinateCubic b j q * normalizedCoordinateCubic c k r =
    (cubicMetricScale p * cubicMetricScale q * cubicMetricScale r) *
      scalarToComplex (inverseCoordinateMetric i * inverseCoordinateMetric j * inverseCoordinateMetric k *
        inverseCoordinateMetric a * inverseCoordinateMetric b * inverseCoordinateMetric c *
        star (coordinateCubic i j k) * star (coordinateCubic a b c) *
        coordinateCubic a i p * coordinateCubic b j q * coordinateCubic c k r) := by
  simp only [normalizedCoordinateCubic, star_mul, cubicMetricScale_star, map_mul, scalarToComplex_star]
  rw [← cubicMetricScale_sq i, ← cubicMetricScale_sq j, ← cubicMetricScale_sq k,
    ← cubicMetricScale_sq a, ← cubicMetricScale_sq b, ← cubicMetricScale_sq c]
  ring

/-- Symbolic comparison of the six-index contractions; no finite domain is expanded. -/
theorem normalizedCoordinateQuintic_eq (p q r : CoordinateIndex) :
    normalizedCoordinateQuintic p q r =
      cubicMetricScale p * cubicMetricScale q * cubicMetricScale r * scalarToComplex (coordinateQuintic p q r) := by
  simp only [normalizedCoordinateQuintic, coordinateQuintic, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  exact normalizedCoordinateQuintic_term p q r i j k a b c

/-- Squared norm of the actual complex cubic coefficient tensor. -/
def normalizedCoordinateCubicNorm : ℂ :=
  ∑ i, ∑ j, ∑ k, normalizedCoordinateCubic i j k * star (normalizedCoordinateCubic i j k)

theorem normalizedCoordinateCubic_norm_term (i j k : CoordinateIndex) :
    normalizedCoordinateCubic i j k * star (normalizedCoordinateCubic i j k) =
      scalarToComplex (inverseCoordinateMetric i * inverseCoordinateMetric j * inverseCoordinateMetric k *
        coordinateCubic i j k * star (coordinateCubic i j k)) := by
  simp only [normalizedCoordinateCubic, star_mul, cubicMetricScale_star, map_mul, scalarToComplex_star]
  rw [← cubicMetricScale_sq i, ← cubicMetricScale_sq j, ← cubicMetricScale_sq k]
  ring

theorem normalizedCoordinateCubicNorm_eq :
    normalizedCoordinateCubicNorm = scalarToComplex coordinateCubicNorm := by
  simp only [normalizedCoordinateCubicNorm, coordinateCubicNorm, coordinateCubicSlice,
    map_sum, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [normalizedCoordinateCubic_norm_term]
  simp only [map_mul, mul_assoc]

/-- The source universal contraction identity is exactly the weighted E identity. -/
theorem normalizedCoordinateQuintic_identity_iff :
    (∀ p q r, normalizedCoordinateQuintic p q r = (1002 : ℂ) * normalizedCoordinateCubic p q r) ↔
      (∀ p q r, coordinateQuintic p q r = (1002 : Scalar) * coordinateCubic p q r) := by
  constructor
  · intro h p q r
    apply scalarToComplex_injective
    have hs : cubicMetricScale p * cubicMetricScale q * cubicMetricScale r ≠ 0 :=
      mul_ne_zero (mul_ne_zero (cubicMetricScale_ne_zero p) (cubicMetricScale_ne_zero q)) (cubicMetricScale_ne_zero r)
    apply (mul_left_cancel₀ hs)
    have hh := h p q r
    rw [normalizedCoordinateQuintic_eq, normalizedCoordinateCubic] at hh
    simpa only [map_mul, map_ofNat, mul_assoc, mul_left_comm] using hh
  · intro h p q r
    rw [normalizedCoordinateQuintic_eq, h, normalizedCoordinateCubic, map_mul, map_ofNat]
    ring

end Atlas.Fischer
