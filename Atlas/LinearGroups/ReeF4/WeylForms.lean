import Atlas.LinearGroups.ReeF4.Weyl
import Atlas.Algebra.Albert.TraceZeroFormIsometry

/-! Quadratic and cubic preservation for Wilson's two Weyl permutations.
The coordinate identities are polynomial identities over any commutative ring;
the installed Albert interpretation below uses characteristic two. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

theorem weylRhoCoordinates_quadratic (w : WilsonCoordinates F) :
    wilsonQuadratic (weylRhoCoordinates w) = wilsonQuadratic w := by
  simp [wilsonQuadratic, wilsonBlockNorm, weylRhoCoordinates]
  ring

theorem weylSigmaCoordinates_quadratic (w : WilsonCoordinates F) :
    wilsonQuadratic (weylSigmaCoordinates w) = wilsonQuadratic w := by
  simp [wilsonQuadratic, wilsonBlockNorm, weylSigmaCoordinates]
  ring

set_option maxHeartbeats 800000 in
theorem weylRhoCoordinates_cubic (w : WilsonCoordinates F) :
    wilsonCubic (weylRhoCoordinates w) = wilsonCubic w := by
  simp [wilsonCubic, wilsonTriple, wilsonBlockNorm, weylRhoCoordinates]
  ring

set_option maxHeartbeats 800000 in
theorem weylSigmaCoordinates_cubic (w : WilsonCoordinates F) :
    wilsonCubic (weylSigmaCoordinates w) = wilsonCubic w := by
  simp [wilsonCubic, wilsonTriple, wilsonBlockNorm, weylSigmaCoordinates]
  ring

variable [CharP F 2]

theorem weylRho_quadratic (w : TraceZero F) :
    traceZeroQuadratic (weylRho w) = traceZeroQuadratic w := by
  change quadraticTrace (weylRho w : Carrier F) = quadraticTrace (w : Carrier F)
  rw [← wilsonQuadratic_coordinates, ← wilsonQuadratic_coordinates,
    weylRho_coordinates, weylRhoCoordinates_quadratic]

theorem weylSigma_quadratic (w : TraceZero F) :
    traceZeroQuadratic (weylSigma w) = traceZeroQuadratic w := by
  change quadraticTrace (weylSigma w : Carrier F) = quadraticTrace (w : Carrier F)
  rw [← wilsonQuadratic_coordinates, ← wilsonQuadratic_coordinates,
    weylSigma_coordinates, weylSigmaCoordinates_quadratic]

theorem weylRho_cubic (w : TraceZero F) :
    traceZeroCubic (weylRho w) = traceZeroCubic w := by
  change norm (weylRho w : Carrier F) = norm (w : Carrier F)
  rw [← wilsonCubic_coordinates, ← wilsonCubic_coordinates,
    weylRho_coordinates, weylRhoCoordinates_cubic]

theorem weylSigma_cubic (w : TraceZero F) :
    traceZeroCubic (weylSigma w) = traceZeroCubic w := by
  change norm (weylSigma w : Carrier F) = norm (w : Carrier F)
  rw [← wilsonCubic_coordinates, ← wilsonCubic_coordinates,
    weylSigma_coordinates, weylSigmaCoordinates_cubic]

theorem weylRho_polar (u v : TraceZero F) :
    traceZeroPolar (weylRho u) (weylRho v) = traceZeroPolar u v :=
  traceZeroPolar_of_quadratic weylRho weylRho_quadratic u v

theorem weylSigma_polar (u v : TraceZero F) :
    traceZeroPolar (weylSigma u) (weylSigma v) = traceZeroPolar u v :=
  traceZeroPolar_of_quadratic weylSigma weylSigma_quadratic u v

theorem weylRho_cross (u v : TraceZero F) :
    traceZeroCross (weylRho u) (weylRho v) = weylRho (traceZeroCross u v) :=
  traceZeroCross_of_forms weylRho weylRho_quadratic weylRho_cubic u v

theorem weylSigma_cross (u v : TraceZero F) :
    traceZeroCross (weylSigma u) (weylSigma v) = weylSigma (traceZeroCross u v) :=
  traceZeroCross_of_forms weylSigma weylSigma_quadratic weylSigma_cubic u v

end Atlas.ReeF4
