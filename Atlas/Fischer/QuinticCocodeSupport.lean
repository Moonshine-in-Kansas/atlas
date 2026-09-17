import Atlas.Fischer.CubicCocodeSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Every contracted code label occurs twice; only the three external labels remain. -/
theorem coordinateTripleWord_contraction (i j k a b c p q r : CoordinateIndex) :
    coordinateTripleWord i j k + coordinateTripleWord a b c + coordinateTripleWord a i p +
      coordinateTripleWord b j q + coordinateTripleWord c k r = coordinateTripleWord p q r := by
  unfold coordinateTripleWord
  calc
    _ = (productTraceCoordinateWord i + productTraceCoordinateWord i) +
      (productTraceCoordinateWord j + productTraceCoordinateWord j) +
      (productTraceCoordinateWord k + productTraceCoordinateWord k) +
      (productTraceCoordinateWord a + productTraceCoordinateWord a) +
      (productTraceCoordinateWord b + productTraceCoordinateWord b) +
      (productTraceCoordinateWord c + productTraceCoordinateWord c) +
      (productTraceCoordinateWord p + productTraceCoordinateWord q + productTraceCoordinateWord r) := by abel
    _ = _ := by simp only [parkerGolay_add_self,zero_add]

def coordinateQuinticCubicProduct (i j k a b c p q r : CoordinateIndex) : Scalar :=
  star (coordinateCubic i j k) * star (coordinateCubic a b c) *
    coordinateCubic a i p * coordinateCubic b j q * coordinateCubic c k r

theorem coordinateQuinticCubicProduct_nonzero_support (i j k a b c p q r : CoordinateIndex)
    (h : coordinateQuinticCubicProduct i j k a b c p q r ≠ 0) :
    coordinateTripleWord p q r ∈ allOneCodeLine := by
  have h1 : coordinateCubic i j k ≠ 0 := by intro hz; simp [coordinateQuinticCubicProduct,hz] at h
  have h2 : coordinateCubic a b c ≠ 0 := by intro hz; simp [coordinateQuinticCubicProduct,hz] at h
  have h3 : coordinateCubic a i p ≠ 0 := by intro hz; simp [coordinateQuinticCubicProduct,hz] at h
  have h4 : coordinateCubic b j q ≠ 0 := by intro hz; simp [coordinateQuinticCubicProduct,hz] at h
  have h5 : coordinateCubic c k r ≠ 0 := by intro hz; simp [coordinateQuinticCubicProduct,hz] at h
  rw [← coordinateTripleWord_contraction i j k a b c p q r]
  exact allOneCodeLine.add_mem (allOneCodeLine.add_mem (allOneCodeLine.add_mem
    (allOneCodeLine.add_mem (coordinateCubic_nonzero_support _ _ _ h1)
      (coordinateCubic_nonzero_support _ _ _ h2)) (coordinateCubic_nonzero_support _ _ _ h3))
      (coordinateCubic_nonzero_support _ _ _ h4)) (coordinateCubic_nonzero_support _ _ _ h5)

/-- The exact six weighted sums vanish termwise outside the actual cocode support. -/
theorem coordinateQuintic_vanish_of_labels (p q r : CoordinateIndex)
    (h0 : coordinateTripleWord p q r ≠ 0) (h1 : coordinateTripleWord p q r ≠ golayOne) :
    coordinateQuintic p q r=0 := by
  have hz (i j k a b c : CoordinateIndex) : coordinateQuinticCubicProduct i j k a b c p q r=0 := by
    by_contra hn
    have hh := (mem_allOneCodeLine _).mp (coordinateQuinticCubicProduct_nonzero_support _ _ _ _ _ _ _ _ _ hn)
    exact hh.elim h0 h1
  unfold coordinateQuintic
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro c hc
  calc
    _ = (inverseCoordinateMetric i * inverseCoordinateMetric j * inverseCoordinateMetric k *
      inverseCoordinateMetric a * inverseCoordinateMetric b * inverseCoordinateMetric c) *
        coordinateQuinticCubicProduct i j k a b c p q r := by
      unfold coordinateQuinticCubicProduct
      ring
    _ = 0 := by rw [hz,mul_zero]

theorem coordinateQuintic_nonzero_support (p q r : CoordinateIndex)
    (h : coordinateQuintic p q r ≠ 0) : coordinateTripleWord p q r ∈ allOneCodeLine := by
  rw [mem_allOneCodeLine]
  by_contra hn
  push_neg at hn
  exact h (coordinateQuintic_vanish_of_labels p q r hn.1 hn.2)

/-- Scalar-sign invariance under every actual even cocode element. -/
theorem coordinateQuintic_even_cocode (d : Cocode) (hd : cocodeParity d=0)
    (p q r : CoordinateIndex) :
    parkerScalarSign (cocodePairing (coordinateTripleWord p q r) d) * coordinateQuintic p q r =
      coordinateQuintic p q r := by
  by_cases hz : coordinateQuintic p q r=0
  · simp [hz]
  rcases (mem_allOneCodeLine _).mp (coordinateQuintic_nonzero_support p q r hz) with hw | hw
  · simp [hw,cocodePairing,parkerScalarSign]
  · have hp : cocodePairing golayOne d=0 := hd
    simp [hw,hp,parkerScalarSign]

end Atlas.Fischer
