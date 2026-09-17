import Atlas.Fischer.CalibratedOctadCubic
import Atlas.Fischer.QuinticCocodeSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def omegaOctadQuintic (t : Omega) (i j k a b c p q r : Octad) : Scalar :=
  star (omegaOctadCubic t i j k) * star (omegaOctadCubic t a b c) *
    omegaOctadCubic t a i p * omegaOctadCubic t b j q * omegaOctadCubic t c k r

/-- The three external coordinate signs are exactly the covariance factor;
every internal coordinate sign cancels twice. -/
theorem omegaOctadQuintic_calibration (t : Omega) (i j k a b c p q r : Octad) :
    omegaOctadQuintic t i j k a b c p q r =
      parkerScalarSign (parkerOmegaGauge t (octadWord p) +
        parkerOmegaGauge t (octadWord q) + parkerOmegaGauge t (octadWord r)) *
      coordinateQuinticCubicProduct (.inr i) (.inr j) (.inr k)
        (.inr a) (.inr b) (.inr c) (.inr p) (.inr q) (.inr r) := by
  unfold omegaOctadQuintic omegaOctadCubic coordinateQuinticCubicProduct
  simp only [star_mul, parkerScalarSign_star]
  have hs (i j k a b c p q r : ParkerBit) :
      parkerScalarSign (i+j+k) * parkerScalarSign (a+b+c) *
        parkerScalarSign (a+i+p) * parkerScalarSign (b+j+q) *
        parkerScalarSign (c+k+r) = parkerScalarSign (p+q+r) := by
    rw [← parkerScalarSign_add, ← parkerScalarSign_add, ← parkerScalarSign_add,
      ← parkerScalarSign_add]
    congr 1
    ring_nf
    simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero, zero_add]
  linear_combination hs (parkerOmegaGauge t (octadWord i))
    (parkerOmegaGauge t (octadWord j)) (parkerOmegaGauge t (octadWord k))
    (parkerOmegaGauge t (octadWord a)) (parkerOmegaGauge t (octadWord b))
    (parkerOmegaGauge t (octadWord c)) (parkerOmegaGauge t (octadWord p))
    (parkerOmegaGauge t (octadWord q)) (parkerOmegaGauge t (octadWord r)) *
      star (coordinateCubic (.inr i) (.inr j) (.inr k)) *
      star (coordinateCubic (.inr a) (.inr b) (.inr c)) *
      coordinateCubic (.inr a) (.inr i) (.inr p) *
      coordinateCubic (.inr b) (.inr j) (.inr q) *
      coordinateCubic (.inr c) (.inr k) (.inr r)

theorem omegaOctadCubic_cycle (t : Omega) (a b c : Octad) :
    omegaOctadCubic t a b c = omegaOctadCubic t c b a := by
  unfold omegaOctadCubic
  have hg : parkerOmegaGauge t (octadWord a) + parkerOmegaGauge t (octadWord b) +
      parkerOmegaGauge t (octadWord c) = parkerOmegaGauge t (octadWord c) +
      parkerOmegaGauge t (octadWord b) + parkerOmegaGauge t (octadWord a) := by abel
  rw [hg, coordinateCubic_swap_first, coordinateCubic_swap_last, coordinateCubic_swap_first]

end Atlas.Fischer
