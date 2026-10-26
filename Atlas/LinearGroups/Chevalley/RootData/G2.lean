import Atlas.LinearGroups.Chevalley.RootData.SmallExceptionalForm
import Atlas.LinearGroups.Chevalley.RootData.G2Table

/-! Actual G2 integral root pairing, reducedness and simple base. -/

namespace Atlas.Chevalley.G2Data
open FiniteRootDatum SmallExceptionalData
abbrev Root := G2Table.Root
abbrev Lattice := Fin 2 → ℤ
private def dualEquiv := dotProductEquiv ℤ (Fin 2)

def datum : FiniteRootDatum.Data 2 12 where
  root := ⟨G2Table.coordinates, G2Table.coordinates_injective⟩
  coroot := ⟨fun a => dualEquiv (G2Table.dualCoordinates a),
    dualEquiv.injective.comp G2Table.dualCoordinates_injective⟩
  root_coroot_two := G2Table.pairing_two
  reflectionIndex := G2Table.reflectionIndex
  reflection_involutive := G2Table.reflection_involutive
  reflection_root := G2Table.reflection_root
  reflection_coroot a b := by
    change dualEquiv (G2Table.dualCoordinates (G2Table.reflectionIndex a b)) = _
    rw [G2Table.reflection_coroot, map_sub, map_smul]
    rfl
  primitive a := ⟨dualEquiv (G2Table.primitiveWitnessCoordinates a),
    G2Table.primitive a⟩
  simpleIndex := G2Table.simpleIndex
  simple_coordinates := G2Table.simple_coordinates
  corootMap := SmallExceptionalData.corootMap G2Table.cartan
  corootMap_injective := SmallExceptionalData.corootMap_injective _ (by
    rw [G2Table.cartan, CartanMatrix.G₂_det]
    decide)
  corootCoordinates := G2Table.corootCoefficientCoordinates
  coroot_coordinates a := by
    apply congrArg dualEquiv
    ext i
    exact (congrFun (G2Table.dual_reconstruct a) i).symm
  simple_coroot_coordinates i := by
    change dualEquiv (G2Table.dualCoordinates (G2Table.simpleIndex i)) = _
    apply congrArg dualEquiv
    ext j
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using
      G2Table.simple_dual_coordinates i j
  root_sign := G2Table.root_sign
  coroot_sign := G2Table.coroot_sign

def pairing : RootPairing Root ℤ Lattice (Module.Dual ℤ Lattice) := datum.pairing
instance reduced : pairing.IsReduced := FiniteRootDatum.Data.reduced datum

def base : pairing.Base := datum.base
noncomputable def baseIndexEquiv : Fin 2 ≃ base.support := datum.baseIndexEquiv

theorem base_cartan (i j : Fin 2) :
    base.cartanMatrix (baseIndexEquiv i) (baseIndexEquiv j) = G2Table.cartan i j :=
  (datum.base_cartan i j).trans (SmallExceptionalData.corootMap_single _ i j)

theorem root_card : Nat.card Root = 12 := by simp [Root, G2Table.Root]

theorem root_image_card : Nat.card (Set.range pairing.root) = 12 := by
  calc
    Nat.card (Set.range pairing.root) = Nat.card Root :=
      Nat.card_congr (Equiv.ofInjective pairing.root pairing.root.injective).symm
    _ = 12 := root_card

theorem base_card : Nat.card base.support = 2 := by
  calc
    Nat.card base.support = Nat.card (Fin 2) := Nat.card_congr baseIndexEquiv.symm
    _ = 2 := by simp

end Atlas.Chevalley.G2Data
