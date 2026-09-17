import Atlas.Fischer.QuinticCocodeSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def parkerTripleSign (e : ParkerStandardGroup) (i j k : CoordinateIndex) : Scalar :=
  parkerScalarSign (parkerCoordinateSign e i + parkerCoordinateSign e j + parkerCoordinateSign e k)

theorem coordinateCubic_parker (e : ParkerStandardGroup) (i j k : CoordinateIndex) :
    parkerTripleSign e i j k * coordinateCubic (parkerCoordinateEquiv e i)
      (parkerCoordinateEquiv e j) (parkerCoordinateEquiv e k) =
        scalarParityAut (parkerStandardParity e).toAdd (coordinateCubic i j k) := by
  have h := cubic_parker_action e (coordinateVector i) (coordinateVector j) (coordinateVector k)
  rw [parkerCoordinateAction_basis, parkerCoordinateAction_basis, parkerCoordinateAction_basis,
    cubic_smul_first, cubic_smul_second, cubic_smul_third] at h
  simpa only [parkerTripleSign, parkerScalarSign_add, coordinateCubic, mul_assoc] using h

theorem parkerTripleSign_contraction (e : ParkerStandardGroup)
    (i j k a b c p q r : CoordinateIndex) :
    parkerTripleSign e i j k * parkerTripleSign e a b c * parkerTripleSign e a i p *
      parkerTripleSign e b j q * parkerTripleSign e c k r = parkerTripleSign e p q r := by
  have h : (parkerCoordinateSign e i + parkerCoordinateSign e j + parkerCoordinateSign e k) +
      (parkerCoordinateSign e a + parkerCoordinateSign e b + parkerCoordinateSign e c) +
      (parkerCoordinateSign e a + parkerCoordinateSign e i + parkerCoordinateSign e p) +
      (parkerCoordinateSign e b + parkerCoordinateSign e j + parkerCoordinateSign e q) +
      (parkerCoordinateSign e c + parkerCoordinateSign e k + parkerCoordinateSign e r) =
        parkerCoordinateSign e p + parkerCoordinateSign e q + parkerCoordinateSign e r := by
    calc
      _ = (parkerCoordinateSign e i + parkerCoordinateSign e i) +
        (parkerCoordinateSign e j + parkerCoordinateSign e j) +
        (parkerCoordinateSign e k + parkerCoordinateSign e k) +
        (parkerCoordinateSign e a + parkerCoordinateSign e a) +
        (parkerCoordinateSign e b + parkerCoordinateSign e b) +
        (parkerCoordinateSign e c + parkerCoordinateSign e c) +
        (parkerCoordinateSign e p + parkerCoordinateSign e q + parkerCoordinateSign e r) := by abel
      _ = _ := by simp only [CharTwo.add_self_eq_zero, zero_add]
  simpa only [parkerTripleSign, parkerScalarSign_add] using congrArg parkerScalarSign h

theorem coordinateQuinticCubicProduct_parker (e : ParkerStandardGroup)
    (i j k a b c p q r : CoordinateIndex) :
    scalarParityAut (parkerStandardParity e).toAdd (coordinateQuinticCubicProduct i j k a b c p q r) =
      parkerTripleSign e p q r * coordinateQuinticCubicProduct
        (parkerCoordinateEquiv e i) (parkerCoordinateEquiv e j) (parkerCoordinateEquiv e k)
        (parkerCoordinateEquiv e a) (parkerCoordinateEquiv e b) (parkerCoordinateEquiv e c)
        (parkerCoordinateEquiv e p) (parkerCoordinateEquiv e q) (parkerCoordinateEquiv e r) := by
  calc
    _ = (parkerTripleSign e i j k * parkerTripleSign e a b c * parkerTripleSign e a i p *
        parkerTripleSign e b j q * parkerTripleSign e c k r) * coordinateQuinticCubicProduct
        (parkerCoordinateEquiv e i) (parkerCoordinateEquiv e j) (parkerCoordinateEquiv e k)
        (parkerCoordinateEquiv e a) (parkerCoordinateEquiv e b) (parkerCoordinateEquiv e c)
        (parkerCoordinateEquiv e p) (parkerCoordinateEquiv e q) (parkerCoordinateEquiv e r) := by
      simp only [coordinateQuinticCubicProduct, map_mul, scalarParityAut_star,
        ← coordinateCubic_parker, star_mul, parkerTripleSign, parkerScalarSign_star]
      ring
    _ = _ := by rw [parkerTripleSign_contraction]

theorem inverseCoordinateMetric_parker (e : ParkerStandardGroup) (i : CoordinateIndex) :
    inverseCoordinateMetric (parkerCoordinateEquiv e i) = inverseCoordinateMetric i := by
  rw [inverseCoordinateMetric, parkerCoordinateEquiv_weight]
  rfl

/-- Full standard Parker-group covariance of the actual six-index contraction. -/
theorem coordinateQuintic_parker (e : ParkerStandardGroup) (p q r : CoordinateIndex) :
    parkerTripleSign e p q r * coordinateQuintic (parkerCoordinateEquiv e p)
      (parkerCoordinateEquiv e q) (parkerCoordinateEquiv e r) =
        scalarParityAut (parkerStandardParity e).toAdd (coordinateQuintic p q r) := by
  unfold coordinateQuintic
  simp only [Finset.mul_sum, map_sum]
  rw [← (parkerCoordinateEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (parkerCoordinateEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [← (parkerCoordinateEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (parkerCoordinateEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [← (parkerCoordinateEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  rw [← (parkerCoordinateEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  simp only [inverseCoordinateMetric_parker]
  have h := coordinateQuinticCubicProduct_parker e i j k a b c p q r
  simp only [coordinateQuinticCubicProduct, map_mul] at h
  simp only [map_mul, inverseCoordinateMetric, map_inv₀, map_ratCast]
  linear_combination (coordinateWeight i : Scalar)⁻¹ * (coordinateWeight j : Scalar)⁻¹ *
    (coordinateWeight k : Scalar)⁻¹ * (coordinateWeight a : Scalar)⁻¹ *
    (coordinateWeight b : Scalar)⁻¹ * (coordinateWeight c : Scalar)⁻¹ * -h
  all_goals simp

end Atlas.Fischer
