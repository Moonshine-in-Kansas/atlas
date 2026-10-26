import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramLattice

/-! Explicit coordinates for the diagram-fixed integral lattice and its
folded simple reflections. No division by two is used. The formulas hold
over every commutative ring; nondegeneracy after reduction is not asserted. -/
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice
variable (R : Type*) [CommRing R]

def foldedCoordinates : (Fin 4 → R) →ₗ[R] (Fin 6 → R) where
  toFun v := ![v 0, v 1, v 2, v 1, v 0, v 3]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' t v := by ext i; fin_cases i <;> rfl

theorem foldedCoordinates_injective : Function.Injective (foldedCoordinates R) := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 5

theorem latticeDiagram_foldedCoordinates (v : Fin 4 → R) :
    latticeDiagram R (foldedCoordinates R v) = foldedCoordinates R v := by
  funext i
  fin_cases i <;> rfl

theorem foldedCoordinates_of_fixed (x : Fin 6 → R) (hx : latticeDiagram R x = x) :
    foldedCoordinates R ![x 0, x 1, x 2, x 5] = x := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact congrFun hx 3
  · exact congrFun hx 4
  · rfl

theorem mem_range_foldedCoordinates_iff (x : Fin 6 → R) :
    x ∈ Set.range (foldedCoordinates R) ↔ latticeDiagram R x = x := by
  constructor
  · rintro ⟨v, rfl⟩
    exact latticeDiagram_foldedCoordinates R v
  · intro hx
    exact ⟨![x 0, x 1, x 2, x 5], foldedCoordinates_of_fixed R x hx⟩

theorem norm_foldedCoordinates (v : Fin 4 → R) :
    norm (foldedCoordinates R v) =
      2 * v 0 ^ 2 + 2 * v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 -
        2 * v 0 * v 1 - 2 * v 1 * v 2 - v 2 * v 3 := by
  change v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 1 ^ 2 + v 0 ^ 2 + v 3 ^ 2 -
    v 0 * v 1 - v 1 * v 2 - v 2 * v 1 - v 1 * v 0 - v 2 * v 3 = _
  ring

def foldedReflection (i : Fin 4) (v : Fin 4 → R) : Fin 4 → R :=
  Function.update v i (match i with
    | 0 => v 1 - v 0
    | 1 => v 0 + v 2 - v 1
    | 2 => 2 * v 1 + v 3 - v 2
    | 3 => v 2 - v 3)

def foldedReflectionLift (i : Fin 4) (x : Fin 6 → R) : Fin 6 → R :=
  match i with
  | 0 => reflection 0 (reflection 4 x)
  | 1 => reflection 1 (reflection 3 x)
  | 2 => reflection 2 x
  | 3 => reflection 5 x

theorem foldedReflection_intertwines (i : Fin 4) (v : Fin 4 → R) :
    foldedCoordinates R (foldedReflection R i v) =
      foldedReflectionLift R i (foldedCoordinates R v) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [foldedCoordinates, foldedReflection, foldedReflectionLift, reflection] <;> ring

end Atlas.Chevalley.TwistedE6
