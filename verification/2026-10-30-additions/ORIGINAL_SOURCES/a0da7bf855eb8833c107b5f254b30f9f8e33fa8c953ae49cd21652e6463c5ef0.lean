import Atlas.LinearGroups.Chevalley.TwistedE6.FoldedLattice
import Atlas.LinearGroups.Chevalley.TwistedE6.PositiveRootOrbits

/-! Explicit witnesses on the existing integral roots. The generator search
is not trusted: Lean checks all 36 word evaluations. Identification with the
actual fixed-group Weyl representatives is a separate continuation. -/
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice

def foldedRootSeed (i : Fin 36) : Fin 6 :=
  if positiveDiagram i = i then 2 else 0

def foldedRootWord : Fin 36 → List (Fin 4) :=
  ![[2, 3],
    [1, 2, 0, 1, 2, 0, 1],
    [2, 1, 2, 0, 1],
    [2, 0, 1, 2, 0, 1],
    [],
    [3],
    [1, 2, 0, 1],
    [3, 1, 2, 0, 1],
    [0, 1, 2, 0, 1],
    [3, 0, 1, 2, 0, 1],
    [0, 1],
    [2, 0, 1],
    [3, 2, 0, 1],
    [1],
    [3, 1],
    [0, 1, 2, 1],
    [3, 0, 1, 2, 1],
    [2, 3, 1],
    [2, 3, 0, 1, 2, 1],
    [1, 2, 3, 0, 1, 2, 1],
    [],
    [1],
    [2, 1],
    [3, 2, 1],
    [1, 2, 1],
    [3, 1, 2, 1],
    [0, 1],
    [3, 0, 1],
    [2, 3, 1, 2, 1],
    [2, 3, 0, 1],
    [0, 1, 2, 3, 0, 1, 2, 1],
    [1, 2, 3, 1, 2, 1],
    [0, 1, 2, 3, 1, 2, 1],
    [1, 2, 3, 0, 1],
    [2, 1, 2, 3, 0, 1],
    [3, 2, 1, 2, 3, 0, 1]]

def foldedRootWordAction (l : List (Fin 4)) (x : Fin 6 → ℤ) : Fin 6 → ℤ :=
  l.foldr (foldedReflectionLift ℤ) x

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem foldedRootWord_representative (i : Fin 36) :
    foldedRootWordAction (foldedRootWord i) (Pi.single (foldedRootSeed i) 1) =
      rootRepresentative i := by
  revert i
  decide

theorem foldedRootSeed_fixed_iff (i : Fin 36) :
    latticeNode (foldedRootSeed i) = foldedRootSeed i ↔ positiveDiagram i = i := by
  revert i
  decide

end Atlas.Chevalley.TwistedE6
