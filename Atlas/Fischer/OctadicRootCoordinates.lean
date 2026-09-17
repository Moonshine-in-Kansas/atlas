import Atlas.Fischer.OctadParkerSections
import Atlas.Fischer.CoordinateEvaluation
import Atlas.Fischer.ParkerOctadProductAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The thirty nonconstant, nonzero words of the actual shortened Golay code. -/
abbrev OctadShortenedHyperplane (O : Octad) :=
  {b : octadShortenedCode O // b ≠ 0 ∧ b ≠ octadShortenedOne O}

theorem octadShortenedHyperplane_weight (O : Octad) (b : OctadShortenedHyperplane O) :
    hammingNorm b.val.val.val = 8 := by
  rcases octadShortened_weights O b.val with h | h | h
  · exact False.elim (b.property.1 (Subtype.ext (Subtype.ext (hammingNorm_eq_zero.mp h))))
  · exact h
  · have hc := octadShortened_complement_weights O b.val
    have hz : b.val + octadShortenedOne O = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      apply hammingNorm_eq_zero.mp
      omega
    have he : b.val = octadShortenedOne O := by
      have hh := congrArg (fun x : octadShortenedCode O => x + octadShortenedOne O) hz
      have hx : octadShortenedOne O + octadShortenedOne O = 0 := by
        rw [← two_smul Bit, show (2 : Bit) = 0 from rfl, zero_smul]
      simpa only [add_assoc, hx, add_zero, zero_add] using hh
    exact False.elim (b.property.2 he)

/-- A marked octad lift and an actual multiplicative section calibrated at Ωo. -/
structure OctadCalibration (O : Octad) where
  octadLift : SignedOctad
  lift_code : octadLift.val.1 = octadWord O
  parkerSection : OctadParkerSection O
  calibrated : parkerSection.lift (octadShortenedOne O) =
    parkerLoopMultiply parkerOmega octadLift.val

def chosenOctadCalibration (O : Octad) : OctadCalibration O where
  octadLift := canonicalOctadLift O
  lift_code := rfl
  parkerSection := octadCalibratedSection O (canonicalOctadLift O).val rfl
  calibrated := octadCalibratedSection_spec O (canonicalOctadLift O).val rfl

abbrev OctadicCharacter (O : Octad) := Module.Dual Bit (octadShortenedCode O)

def calibratedHyperplaneLift {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) : SignedOctad :=
  ⟨Q.parkerSection.lift b.val, octadShortenedHyperplane_weight O b⟩

/-- The source's y_b is the actual signed octad coordinate of q_b. -/
def calibratedHyperplaneVector {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) : Coordinates :=
  signedOctadVector (calibratedHyperplaneLift Q b)

def octadicAxisPart (O : Octad) : Coordinates :=
  -(∑ i ∈ O.val, u i) + ∑ i ∈ O.valᶜ, u i

/-- The literal calibrated formula (5.1), with characters recorded additively
over F₂ and evaluated by the actual scalar sign. -/
def octadicRoot {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) : Coordinates :=
  (1 / 2 : Scalar) • (octadicAxisPart O +
    (theta * parkerScalarSign (χ (octadShortenedOne O))) • signedOctadVector Q.octadLift +
    ∑ b : OctadShortenedHyperplane O,
      parkerScalarSign (χ b.val) • calibratedHyperplaneVector Q b)

theorem calibratedHyperplaneVector_norm {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (calibratedHyperplaneVector Q b) (calibratedHyperplaneVector Q b) = 1 :=
  signedOctadVector_norm _

/-- The exact linear character relating two calibrated choices. -/
def octadCalibrationDifference {O : Octad} (Q R : OctadCalibration O) : OctadicCharacter O :=
  Q.parkerSection.difference R.parkerSection

theorem calibratedHyperplaneVector_change {O : Octad} (Q R : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    calibratedHyperplaneVector R b = parkerScalarSign (octadCalibrationDifference Q R b.val) •
      calibratedHyperplaneVector Q b := by
  have he : calibratedHyperplaneLift R b =
      signedOctadSign (octadCalibrationDifference Q R b.val) (calibratedHyperplaneLift Q b) :=
    Subtype.ext (Q.parkerSection.difference_lift R.parkerSection b.val)
  change signedOctadVector _ = _
  rw [he, signedOctadSign_vector]
  rfl

theorem calibratedOctadVector_change {O : Octad} (Q R : OctadCalibration O) :
    signedOctadVector R.octadLift =
      parkerScalarSign (octadCalibrationDifference Q R (octadShortenedOne O)) •
        signedOctadVector Q.octadLift := by
  have he : R.octadLift =
      signedOctadSign (octadCalibrationDifference Q R (octadShortenedOne O)) Q.octadLift :=
    Subtype.ext (ParkerSection.calibrated_change Q.parkerSection R.parkerSection _ _ _
      Q.calibrated R.calibrated)
  rw [he, signedOctadSign_vector]

/-- Changing either calibrated choice translates one and the same character in
every coefficient. This is equality of the actual vectors, before taking rays. -/
theorem octadicRoot_change {O : Octad} (Q R : OctadCalibration O) (χ : OctadicCharacter O) :
    octadicRoot R χ = octadicRoot Q (χ + octadCalibrationDifference Q R) := by
  simp only [octadicRoot, calibratedOctadVector_change Q R, calibratedHyperplaneVector_change Q R,
    LinearMap.add_apply, parkerScalarSign_add, smul_smul, mul_assoc]

end Atlas.Fischer
