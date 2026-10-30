import F4Work.F4IntegralOperatorData
import F4Work.F4AlbertScalarIdentities
import Atlas.LinearGroups.F4.SimpleCorootActions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Shared definitions for the source-only formula split. The definitions
and four direct imports are copied from the reviewed monolithic source. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.Albert
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

/-- Literal 27-coordinate entries; diagonal coordinates come first. -/
def albertCoordinates (x : Carrier R) (j : Fin 27) : R :=
  coordinateEquiv x (Atlas.F4.albertCoordinateOfFin j)

def simplePolynomialMatrix (i : Fin 8) (t : R) : Matrix (Fin 27) (Fin 27) R :=
  1 + t • (simpleMatrix i).map (Int.castRingHom R) +
    t^2 • (simpleSecondMatrix i).map (Int.castRingHom R)

end Atlas.Chevalley.Comparison.F4
