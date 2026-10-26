import Atlas.GroupTheory.Amalgam.TwoGroups
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.PUnit

/-! A small kernel-checked regression: C₂ ∗ C₂ surjects onto S₃. Only the
six-element target calculation uses `decide`; the universal property is generic. -/

namespace Atlas.GroupTheory.Amalgam.C2Example

abbrev C2 := Equiv.Perm (Fin 2)
abbrev S3 := Equiv.Perm (Fin 3)

theorem card_C2 : Fintype.card C2 = 2 := by decide
theorem card_S3 : Fintype.card S3 = 6 := by decide

def first : C2 →* S3 where
  toFun x := if x = 1 then 1 else Equiv.swap 0 1
  map_one' := by decide
  map_mul' := by decide

def second : C2 →* S3 where
  toFun x := if x = 1 then 1 else Equiv.swap 1 2
  map_one' := by decide
  map_mul' := by decide

def trivialMap : PUnit →* C2 := 1

abbrev FreeProduct := TwoGroupCompletion trivialMap trivialMap

def onto : FreeProduct →* S3 :=
  twoGroupLift trivialMap trivialMap first second (by ext x; cases x; rfl)

def leftGenerator : FreeProduct := twoGroupLeft trivialMap trivialMap (Equiv.swap 0 1)
def rightGenerator : FreeProduct := twoGroupRight trivialMap trivialMap (Equiv.swap 0 1)

@[simp] theorem onto_left : onto leftGenerator = Equiv.swap 0 1 := by
  rw [onto, leftGenerator, twoGroupLift_left]
  decide

@[simp] theorem onto_right : onto rightGenerator = Equiv.swap 1 2 := by
  rw [onto, rightGenerator, twoGroupLift_right]
  decide

/-- An explicit six-word cover of S₃; this is not a permutation certificate
for any ATLAS group. -/
theorem six_words (x : S3) :
    x = 1 ∨ x = Equiv.swap 0 1 ∨ x = Equiv.swap 1 2 ∨
      x = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
      x = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
      x = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
  revert x
  decide

theorem onto_surjective : Function.Surjective onto := by
  intro x
  rcases six_words x with h | h | h | h | h | h
  · exact ⟨1, by simpa using h.symm⟩
  · exact ⟨leftGenerator, by simpa using h.symm⟩
  · exact ⟨rightGenerator, by simpa using h.symm⟩
  · exact ⟨leftGenerator * rightGenerator, by simpa using h.symm⟩
  · exact ⟨rightGenerator * leftGenerator, by simpa using h.symm⟩
  · exact ⟨leftGenerator * rightGenerator * leftGenerator, by simpa using h.symm⟩

end Atlas.GroupTheory.Amalgam.C2Example
