import Atlas.LinearGroups.Chevalley.RootData.ExceptionalForm
import Atlas.LinearGroups.Chevalley.RootData.E7Table

/-! Concrete E7 integral root pairing, reducedness and simple base. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Atlas.Chevalley.E7Data
open FiniteSimplyLaced ExceptionalData
abbrev Root := E7Table.Root
abbrev Lattice := Fin 7 → ℤ

private theorem reflect_eq (i : Fin 7) (x : Lattice) :
    FiniteSimplyLaced.reflectVector (ExceptionalData.form 7) i x =
      E7Table.reflect i x := ExceptionalData.reflectVector_eq_update 7 i x

private theorem wordAction_eq (w : List (Fin 7)) (x : Lattice) :
    FiniteSimplyLaced.wordAction (ExceptionalData.form 7) w x =
      E7Table.wordAction w x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    change FiniteSimplyLaced.wordAction (ExceptionalData.form 7) w
        (FiniteSimplyLaced.reflectVector (ExceptionalData.form 7) i x) =
      E7Table.wordAction w (E7Table.reflect i x)
    rw [ih, reflect_eq]

/-- Concrete arithmetic data, all finite claims supplied by actual checked tables. -/
def datum : FiniteSimplyLaced.Data 7 126 where
  form := ExceptionalData.form 7
  form_symm := ExceptionalData.form_symm 7
  form_injective := ExceptionalData.form_injective 7 (by decide) (by decide)
  root := ⟨E7Table.coordinates, E7Table.coordinates_injective⟩
  norm_two a := by
    change ExceptionalData.form 7 (E7Table.coordinates a) (E7Table.coordinates a) = 2
    simpa only [ExceptionalData.form, Matrix.toBilin'_apply, E7Table.pair] using E7Table.root_norm a
  simpleIndex := E7Table.simpleIndex
  simple_coordinates := E7Table.simple_coordinates
  simpleReflectionIndex := E7Table.simpleReflectionIndex
  simple_reflection_coordinates i a := by
    rw [reflect_eq]
    exact E7Table.simple_reflection_coordinates i a
  word := E7Table.rootWord
  word_coordinates a := by
    rw [wordAction_eq]
    exact E7Table.root_word_coordinates a
  sign_coherent := E7Table.sign_coherent

/-- The actual E7 root datum on the integral root lattice and its exact dual. -/
def pairing : RootPairing Root ℤ Lattice (Module.Dual ℤ Lattice) := datum.pairing

instance reduced : pairing.IsReduced := FiniteSimplyLaced.Data.reduced datum

/-- The genuine standard-coordinate simple-root base. -/
def base : pairing.Base := datum.base

noncomputable def baseIndexEquiv : Fin 7 ≃ base.support := datum.baseIndexEquiv

theorem base_cartan (i j : Fin 7) :
    base.cartanMatrix (baseIndexEquiv i) (baseIndexEquiv j) = CartanMatrix.E 7 i j :=
  (datum.base_cartan i j).trans (Matrix.toBilin'_single _ _ _)

theorem root_card : Nat.card Root = 126 := by
  simp [Root, E7Table.Root]

theorem root_image_card : Nat.card (Set.range pairing.root) = 126 := by
  calc
    Nat.card (Set.range pairing.root) = Nat.card Root :=
      Nat.card_congr (Equiv.ofInjective pairing.root pairing.root.injective).symm
    _ = 126 := root_card

theorem base_card : Nat.card base.support = 7 := by
  calc
    Nat.card base.support = Nat.card (Fin 7) := Nat.card_congr baseIndexEquiv.symm
    _ = 7 := by simp

end Atlas.Chevalley.E7Data
