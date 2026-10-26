import Atlas.Comparisons.Exceptional.E6.Lattice
import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramCoordinates

/-! The order-two E6 diagram symmetry on the existing integral coordinate
lattice. The lattice numbering has edges 01,12,23,34,25. These identities
hold over every commutative ring; no field characteristic is excluded. -/
namespace Atlas.Chevalley.TwistedE6

open Atlas.Comparisons.E6Lattice

variable (R : Type*) [CommRing R]

theorem latticeDiagram_norm (x : Fin 6 → R) :
    Atlas.Comparisons.E6Lattice.norm (latticeDiagram R x) =
      Atlas.Comparisons.E6Lattice.norm x := by
  simp only [Atlas.Comparisons.E6Lattice.norm, latticeDiagram_apply]
  change x 4^2 + x 3^2 + x 2^2 + x 1^2 + x 0^2 + x 5^2 -
    x 4*x 3 - x 3*x 2 - x 2*x 1 - x 1*x 0 - x 2*x 5 = _
  ring

theorem latticeDiagram_polar (x y : Fin 6 → R) :
    (form R).polarBilin (latticeDiagram R x) (latticeDiagram R y) =
      (form R).polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ← map_add, form_apply, latticeDiagram_norm]

end Atlas.Chevalley.TwistedE6
