import Atlas.Fischer.QuinticCocodeSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def cocodeScalarCharacter (d : Cocode) (w : golay) : Scalar :=
  parkerScalarSign (cocodePairing w d)

theorem cocodeScalarCharacter_add (d : Cocode) (u v : golay) :
    cocodeScalarCharacter d (u+v)=cocodeScalarCharacter d u*cocodeScalarCharacter d v := by
  simp only [cocodeScalarCharacter,cocodePairing,map_add,parkerScalarSign_add]

theorem cocodeScalarCharacter_contraction (d : Cocode) (i j k a b c p q r : CoordinateIndex) :
    cocodeScalarCharacter d (coordinateTripleWord i j k) *
      cocodeScalarCharacter d (coordinateTripleWord a b c) *
      cocodeScalarCharacter d (coordinateTripleWord a i p) *
      cocodeScalarCharacter d (coordinateTripleWord b j q) *
      cocodeScalarCharacter d (coordinateTripleWord c k r) =
        cocodeScalarCharacter d (coordinateTripleWord p q r) := by
  have h := congrArg (cocodeScalarCharacter d) (coordinateTripleWord_contraction i j k a b c p q r)
  simpa only [cocodeScalarCharacter_add] using h

/-- All five cubic factors transform, including the two conjugated factors. -/
theorem coordinateQuinticCubicProduct_cocode (d : Cocode) (i j k a b c p q r : CoordinateIndex) :
    scalarParityAut (cocodeParity d) (coordinateQuinticCubicProduct i j k a b c p q r) =
      cocodeScalarCharacter d (coordinateTripleWord p q r) *
        coordinateQuinticCubicProduct i j k a b c p q r := by
  calc
    _ = (cocodeScalarCharacter d (coordinateTripleWord i j k) *
      cocodeScalarCharacter d (coordinateTripleWord a b c) *
      cocodeScalarCharacter d (coordinateTripleWord a i p) *
      cocodeScalarCharacter d (coordinateTripleWord b j q) *
      cocodeScalarCharacter d (coordinateTripleWord c k r)) *
        coordinateQuinticCubicProduct i j k a b c p q r := by
      simp only [coordinateQuinticCubicProduct,map_mul,scalarParityAut_star,
        ← coordinateCubic_cocode,star_mul,parkerScalarSign_star,cocodeScalarCharacter]
      ring
    _ = _ := by rw [cocodeScalarCharacter_contraction]

theorem inverseCoordinateMetric_cocode (d : Cocode) (i : CoordinateIndex) :
    scalarParityAut (cocodeParity d) (inverseCoordinateMetric i)=inverseCoordinateMetric i := by
  simp only [inverseCoordinateMetric,map_inv₀,map_ratCast]

/-- Full odd/even cocode covariance of the exact weighted quintic tensor.
This is proved before and independently of K=1002C. -/
theorem coordinateQuintic_cocode (d : Cocode) (p q r : CoordinateIndex) :
    scalarParityAut (cocodeParity d) (coordinateQuintic p q r) =
      cocodeScalarCharacter d (coordinateTripleWord p q r) * coordinateQuintic p q r := by
  unfold coordinateQuintic
  simp only [map_sum,Finset.mul_sum]
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
  have hfactor : inverseCoordinateMetric i * inverseCoordinateMetric j * inverseCoordinateMetric k *
      inverseCoordinateMetric a * inverseCoordinateMetric b * inverseCoordinateMetric c *
      star (coordinateCubic i j k) * star (coordinateCubic a b c) * coordinateCubic a i p *
      coordinateCubic b j q * coordinateCubic c k r =
      (inverseCoordinateMetric i * inverseCoordinateMetric j * inverseCoordinateMetric k *
      inverseCoordinateMetric a * inverseCoordinateMetric b * inverseCoordinateMetric c) *
        coordinateQuinticCubicProduct i j k a b c p q r := by
    unfold coordinateQuinticCubicProduct
    ring
  rw [hfactor,map_mul,coordinateQuinticCubicProduct_cocode]
  simp only [map_mul,inverseCoordinateMetric_cocode]
  ring

end Atlas.Fischer
