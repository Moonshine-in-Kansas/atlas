import Atlas.Comparisons.Exceptional.E6.BinaryOrthogonal
import Atlas.Comparisons.Exceptional.E6.RootRepresentatives

/-! Short reflection words reach every integral root from one simple root.
The table is discovery data; its complete action is checked in Lean. -/
namespace Atlas.Comparisons.E6Lattice

def wordAction : List (Fin 6) → (Fin 6 → ℤ) → (Fin 6 → ℤ)
  | [], x => x
  | i :: w, x => reflection i (wordAction w x)

def wordIsometry : List (Fin 6) → IntegralWeyl
  | [] => 1
  | i :: w => ⟨simpleReflection ℤ i,simpleReflection_mem ℤ i⟩ * wordIsometry w

theorem wordIsometry_action (w : List (Fin 6)) (x : Fin 6 → ℤ) :
    (wordIsometry w).val.val x = wordAction w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change reflection i ((wordIsometry w).val.val x) = reflection i (wordAction w x)
    rw [ih]

def representativeWord : Fin 36 → List (Fin 6) :=
  ![[2,5,1,2,0,1],
    [3,4,2,3,1,2,0,1],
    [2,3,1,2,0,1],
    [4,2,3,1,2,0,1],
    [1,2,0,1],
    [5,1,2,0,1],
    [3,1,2,0,1],
    [5,3,1,2,0,1],
    [4,3,1,2,0,1],
    [5,4,3,1,2,0,1],
    [0,1],
    [2,0,1],
    [5,2,0,1],
    [3,2,0,1],
    [5,3,2,0,1],
    [4,3,2,0,1],
    [5,4,3,2,0,1],
    [2,5,3,2,0,1],
    [2,5,4,3,2,0,1],
    [3,2,5,4,3,2,0,1],
    [],
    [1],
    [2,1],
    [5,2,1],
    [3,2,1],
    [5,3,2,1],
    [4,3,2,1],
    [5,4,3,2,1],
    [2,5,3,2,1],
    [2,5,4,3,2,1],
    [3,2,5,4,3,2,1],
    [1,2,5,3,2,1],
    [1,2,5,4,3,2,1],
    [3,1,2,5,4,3,2,1],
    [2,3,1,2,5,4,3,2,1],
    [5,2,3,1,2,5,4,3,2,1]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Check36 short words acting on one vector, not a group enumeration.
theorem representativeWord_action (i : Fin 36) :
    wordAction (representativeWord i) (simpleRoot 0) = rootRepresentative i := by
  revert i
  decide

theorem weyl_reaches_every_root (x : Fin 6 → ℤ) (hx : norm x = 1) :
    ∃ g : IntegralWeyl, g.val.val (simpleRoot 0) = x := by
  obtain ⟨i,hi | hi⟩ := root_representative_exhaustion x hx
  · refine ⟨wordIsometry (representativeWord i),?_⟩
    rw [wordIsometry_action,representativeWord_action,hi]
  · refine ⟨wordIsometry (representativeWord i) *
      ⟨simpleReflection ℤ 0,simpleReflection_mem ℤ 0⟩,?_⟩
    change (wordIsometry (representativeWord i)).val.val (reflection 0 (simpleRoot 0)) = x
    rw [show reflection 0 (simpleRoot 0) = -simpleRoot 0 by decide,map_neg,
      wordIsometry_action,representativeWord_action,hi]

end Atlas.Comparisons.E6Lattice
