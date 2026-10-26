import Atlas.LinearGroups.Chevalley.RootData.ExceptionalForm
import Atlas.LinearGroups.Chevalley.RootData.E8Table

/-! Concrete E8 integral root pairing, reducedness and simple base. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Atlas.Chevalley.E8Data
open FiniteSimplyLaced ExceptionalData
abbrev Root := E8Table.Root
abbrev Lattice := Fin 8 → ℤ

private theorem reflect_eq (i : Fin 8) (x : Lattice) :
    FiniteSimplyLaced.reflectVector (ExceptionalData.form 8) i x =
      E8Table.reflect i x := ExceptionalData.reflectVector_eq_update 8 i x

private theorem wordAction_eq (w : List (Fin 8)) (x : Lattice) :
    FiniteSimplyLaced.wordAction (ExceptionalData.form 8) w x =
      E8Table.wordAction w x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    change FiniteSimplyLaced.wordAction (ExceptionalData.form 8) w
        (FiniteSimplyLaced.reflectVector (ExceptionalData.form 8) i x) =
      E8Table.wordAction w (E8Table.reflect i x)
    rw [ih, reflect_eq]

/-- Concrete arithmetic data, all finite claims supplied by actual checked tables. -/
def datum : FiniteSimplyLaced.Data 8 240 where
  form := ExceptionalData.form 8
  form_symm := ExceptionalData.form_symm 8
  form_injective := ExceptionalData.form_injective 8 (by decide) (by decide)
  root := ⟨E8Table.coordinates, E8Table.coordinates_injective⟩
  norm_two a := by
    change ExceptionalData.form 8 (E8Table.coordinates a) (E8Table.coordinates a) = 2
    simpa only [ExceptionalData.form, Matrix.toBilin'_apply, E8Table.pair] using E8Table.root_norm a
  simpleIndex := E8Table.simpleIndex
  simple_coordinates := E8Table.simple_coordinates
  simpleReflectionIndex := E8Table.simpleReflectionIndex
  simple_reflection_coordinates i a := by
    rw [reflect_eq]
    exact E8Table.simple_reflection_coordinates i a
  word := E8Table.rootWord
  word_coordinates a := by
    rw [wordAction_eq]
    exact E8Table.root_word_coordinates a
  sign_coherent := E8Table.sign_coherent

/-- The actual E8 root datum on the integral root lattice and its exact dual. -/
def pairing : RootPairing Root ℤ Lattice (Module.Dual ℤ Lattice) := datum.pairing

instance reduced : pairing.IsReduced := FiniteSimplyLaced.Data.reduced datum

/-- The genuine standard-coordinate simple-root base. -/
def base : pairing.Base := datum.base

noncomputable def baseIndexEquiv : Fin 8 ≃ base.support := datum.baseIndexEquiv

theorem base_cartan (i j : Fin 8) :
    base.cartanMatrix (baseIndexEquiv i) (baseIndexEquiv j) = CartanMatrix.E 8 i j :=
  (datum.base_cartan i j).trans (Matrix.toBilin'_single _ _ _)

theorem root_card : Nat.card Root = 240 := by
  simp [Root, E8Table.Root]

theorem root_image_card : Nat.card (Set.range pairing.root) = 240 := by
  calc
    Nat.card (Set.range pairing.root) = Nat.card Root :=
      Nat.card_congr (Equiv.ofInjective pairing.root pairing.root.injective).symm
    _ = 240 := root_card

theorem base_card : Nat.card base.support = 8 := by
  calc
    Nat.card base.support = Nat.card (Fin 8) := Nat.card_congr baseIndexEquiv.symm
    _ = 8 := by simp

end Atlas.Chevalley.E8Data
