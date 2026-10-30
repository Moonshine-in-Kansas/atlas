import FamilyWork.FoldedRootWords

/-! The folded reflection words respect the diagram and reach both members of
every exchanged root pair. These are integral-lattice statements; actual group
representatives and their conjugation action are separate obligations. -/
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice

variable (R : Type*) [CommRing R]

theorem foldedReflectionLift_diagram (i : Fin 4) (x : Fin 6 → R) :
    latticeDiagram R (foldedReflectionLift R i x) =
      foldedReflectionLift R i (latticeDiagram R x) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [foldedReflectionLift, reflection, latticeDiagram_apply, latticeNode] <;> ring

theorem foldedReflectionLift_norm (i : Fin 4) (x : Fin 6 → R) :
    Atlas.Comparisons.E6Lattice.norm (foldedReflectionLift R i x) =
      Atlas.Comparisons.E6Lattice.norm x := by
  fin_cases i <;> simp only [foldedReflectionLift, reflection_norm]

theorem foldedReflectionLift_involutive (i : Fin 4) :
    Function.Involutive (foldedReflectionLift R i) := by
  intro x
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [foldedReflectionLift, reflection] <;> ring

theorem foldedRootWordAction_diagram (l : List (Fin 4)) (x : Fin 6 → ℤ) :
    latticeDiagram ℤ (foldedRootWordAction l x) =
      foldedRootWordAction l (latticeDiagram ℤ x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change latticeDiagram ℤ (foldedReflectionLift ℤ i (foldedRootWordAction l x)) = _
    rw [foldedReflectionLift_diagram, ih]
    rfl

theorem foldedRootWordAction_norm (l : List (Fin 4)) (x : Fin 6 → ℤ) :
    Atlas.Comparisons.E6Lattice.norm (foldedRootWordAction l x) =
      Atlas.Comparisons.E6Lattice.norm x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change Atlas.Comparisons.E6Lattice.norm
      (foldedReflectionLift ℤ i (foldedRootWordAction l x)) = _
    rw [foldedReflectionLift_norm, ih]

theorem foldedRootWordAction_injective (l : List (Fin 4)) :
    Function.Injective (foldedRootWordAction l) := by
  induction l with
  | nil => exact Function.injective_id
  | cons i l ih =>
    exact (foldedReflectionLift_involutive ℤ i).injective.comp ih

theorem foldedRootWord_partner (i : Fin 36) :
    foldedRootWordAction (foldedRootWord i)
      (Pi.single (latticeNode (foldedRootSeed i)) 1) =
      rootRepresentative (positiveDiagram i) := by
  rw [← latticeDiagram_single ℤ, ← foldedRootWordAction_diagram,
    foldedRootWord_representative, latticeDiagram_rootRepresentative]

end Atlas.Chevalley.TwistedE6
