import Atlas.LinearGroups.Chevalley.RootData.SmallExceptionalForm
import Atlas.LinearGroups.Chevalley.RootData.F4Table

/-! Actual F4 integral root pairing, reducedness and simple base. -/

namespace Atlas.Chevalley.F4Data
open FiniteRootDatum SmallExceptionalData
abbrev Root := F4Table.Root
abbrev Lattice := Fin 4 → ℤ
private def dualEquiv := dotProductEquiv ℤ (Fin 4)

def datum : FiniteRootDatum.Data 4 48 where
  root := ⟨F4Table.coordinates, F4Table.coordinates_injective⟩
  coroot := ⟨fun a => dualEquiv (F4Table.dualCoordinates a),
    dualEquiv.injective.comp F4Table.dualCoordinates_injective⟩
  root_coroot_two := F4Table.pairing_two
  reflectionIndex := F4Table.reflectionIndex
  reflection_involutive := F4Table.reflection_involutive
  reflection_root := F4Table.reflection_root
  reflection_coroot a b := by
    change dualEquiv (F4Table.dualCoordinates (F4Table.reflectionIndex a b)) = _
    rw [F4Table.reflection_coroot, map_sub, map_smul]
    rfl
  primitive a := ⟨dualEquiv (F4Table.primitiveWitnessCoordinates a),
    F4Table.primitive a⟩
  simpleIndex := F4Table.simpleIndex
  simple_coordinates := F4Table.simple_coordinates
  corootMap := SmallExceptionalData.corootMap F4Table.cartan
  corootMap_injective := SmallExceptionalData.corootMap_injective _ (by
    rw [F4Table.cartan, CartanMatrix.F₄_det]
    decide)
  corootCoordinates := F4Table.corootCoefficientCoordinates
  coroot_coordinates a := by
    apply congrArg dualEquiv
    ext i
    exact (congrFun (F4Table.dual_reconstruct a) i).symm
  simple_coroot_coordinates i := by
    change dualEquiv (F4Table.dualCoordinates (F4Table.simpleIndex i)) = _
    apply congrArg dualEquiv
    ext j
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using
      F4Table.simple_dual_coordinates i j
  root_sign := F4Table.root_sign
  coroot_sign := F4Table.coroot_sign

def pairing : RootPairing Root ℤ Lattice (Module.Dual ℤ Lattice) := datum.pairing
instance reduced : pairing.IsReduced := FiniteRootDatum.Data.reduced datum

def base : pairing.Base := datum.base
noncomputable def baseIndexEquiv : Fin 4 ≃ base.support := datum.baseIndexEquiv

theorem base_cartan (i j : Fin 4) :
    base.cartanMatrix (baseIndexEquiv i) (baseIndexEquiv j) = F4Table.cartan i j :=
  (datum.base_cartan i j).trans (SmallExceptionalData.corootMap_single _ i j)

theorem root_card : Nat.card Root = 48 := by simp [Root, F4Table.Root]

theorem root_image_card : Nat.card (Set.range pairing.root) = 48 := by
  calc
    Nat.card (Set.range pairing.root) = Nat.card Root :=
      Nat.card_congr (Equiv.ofInjective pairing.root pairing.root.injective).symm
    _ = 48 := root_card

theorem base_card : Nat.card base.support = 4 := by
  calc
    Nat.card base.support = Nat.card (Fin 4) := Nat.card_congr baseIndexEquiv.symm
    _ = 4 := by simp

end Atlas.Chevalley.F4Data
