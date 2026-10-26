import Atlas.LinearGroups.Chevalley.RootData.RootWordLabels
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Tactic.Module

/-! Literal lists underlying the exhaustive two-simple-support enumerations.
Only root permutations and Cartan pairings enter these equalities. -/
noncomputable section
namespace Atlas.Chevalley.RootData
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem rootWordLabels_two_literal (i j : b.support)
    (hji : b.cartanMatrix j i = 0) :
    rootWordLabels P b [i,j] = [i.val,j.val] := by
  have hpji : P.pairing j.val i.val = 0 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val,
      show P.pairingIn ℤ j.val i.val = 0 from hji]
    simp
  have he : P.reflectionPerm i.val j.val = j.val := by
    apply P.root.injective
    simp only [P.root_reflectionPerm,P.reflection_apply,P.root_coroot'_eq_pairing,hpji]
    module
  simp only [rootWordLabels,List.map_cons,List.map_nil,he]

theorem rootWordLabels_three_literal (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    rootWordLabels P b [i,j,i] = [i.val,P.reflectionPerm i.val j.val,j.val] := by
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val,
      show P.pairingIn ℤ i.val j.val = -1 from hij]
    simp
  have hpji : P.pairing j.val i.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val,
      show P.pairingIn ℤ j.val i.val = -1 from hji]
    simp
  have he : P.reflectionPerm i.val (P.reflectionPerm j.val i.val) = j.val := by
    apply P.root.injective
    simp only [P.root_reflectionPerm,P.reflection_apply,map_sub,map_smul,
      P.root_coroot'_eq_pairing,P.pairing_same,hpij,hpji]
    module
  simp only [rootWordLabels,List.map_cons,List.map_nil,he]

theorem rootWordLabels_four_literal (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    rootWordLabels P b [i,j,i,j] =
      [i.val,P.reflectionPerm i.val j.val,P.reflectionPerm j.val i.val,j.val] := by
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val,
      show P.pairingIn ℤ i.val j.val = -1 from hij]
    simp
  have hpji : P.pairing j.val i.val = -2 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val,
      show P.pairingIn ℤ j.val i.val = -2 from hji]
    simp
  have h3 : P.reflectionPerm i.val (P.reflectionPerm j.val i.val) =
      P.reflectionPerm j.val i.val := by
    apply P.root.injective
    simp only [P.root_reflectionPerm,P.reflection_apply,map_sub,map_smul,
      P.root_coroot'_eq_pairing,P.pairing_same,hpij,hpji]
    module
  have h4 : P.reflectionPerm i.val (P.reflectionPerm j.val
      (P.reflectionPerm i.val j.val)) = j.val := by
    apply P.root.injective
    simp only [P.root_reflectionPerm,P.reflection_apply,map_sub,map_smul,
      P.root_coroot'_eq_pairing,P.pairing_same,hpij,hpji]
    module
  simp only [rootWordLabels,List.map_cons,List.map_nil]
  rw [h4,h3]

theorem rootWordLabels_six_literal (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    rootWordLabels P b [i,j,i,j,i,j] =
      [i.val,P.reflectionPerm i.val j.val,
        P.reflectionPerm i.val (P.reflectionPerm j.val i.val),
        P.reflectionPerm j.val (P.reflectionPerm i.val j.val),
        P.reflectionPerm j.val i.val,j.val] := by
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val,
      show P.pairingIn ℤ i.val j.val = -1 from hij]
    simp
  have hpji : P.pairing j.val i.val = -3 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val,
      show P.pairingIn ℤ j.val i.val = -3 from hji]
    simp
  have h4 : P.reflectionPerm i.val (P.reflectionPerm j.val
      (P.reflectionPerm i.val j.val)) =
      P.reflectionPerm j.val (P.reflectionPerm i.val j.val) := by
    apply P.root.injective
    simp only [P.root_reflectionPerm,P.reflection_apply,map_sub,map_smul,
      P.root_coroot'_eq_pairing,P.pairing_same,hpij,hpji]
    module
  have h5 : P.reflectionPerm i.val (P.reflectionPerm j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val i.val))) =
      P.reflectionPerm j.val i.val := by
    apply P.root.injective
    simp only [P.root_reflectionPerm,P.reflection_apply,map_sub,map_smul,
      P.root_coroot'_eq_pairing,P.pairing_same,hpij,hpji]
    module
  have h6 : P.reflectionPerm i.val (P.reflectionPerm j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val
        (P.reflectionPerm i.val j.val)))) = j.val := by
    apply P.root.injective
    simp only [P.root_reflectionPerm,P.reflection_apply,map_sub,map_smul,
      P.root_coroot'_eq_pairing,P.pairing_same,hpij,hpji]
    module
  simp only [rootWordLabels,List.map_cons,List.map_nil]
  rw [h6,h5,h4]

end Atlas.Chevalley.RootData
