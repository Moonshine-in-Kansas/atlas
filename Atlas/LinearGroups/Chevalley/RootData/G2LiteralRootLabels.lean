import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Tactic.Module

/-! Source candidate: labels of the four literal G2 Weyl-conjugate families.
This is a root-pairing calculation, independent of any constructed group. -/

noncomputable section
namespace Atlas.Chevalley.RootData
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]

/-- The words j,ij,i,ji acting on i,i,j,j have the exact integral root
coordinates α+β,2α+β,3α+β,3α+2β. The roots need not be ambient simple roots. -/
theorem g2_literal_root_labels (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3) :
    P.root (P.reflectionPerm j i) = (1:ℤ) • P.root i + (1:ℤ) • P.root j ∧
    P.root (P.reflectionPerm i (P.reflectionPerm j i)) =
      (2:ℤ) • P.root i + (1:ℤ) • P.root j ∧
    P.root (P.reflectionPerm i j) = (3:ℤ) • P.root i + (1:ℤ) • P.root j ∧
    P.root (P.reflectionPerm j (P.reflectionPerm i j)) =
      (3:ℤ) • P.root i + (2:ℤ) • P.root j := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j,hij]
    simp
  have hpji : P.pairing j i = -3 := by
    rw [← P.algebraMap_pairingIn ℤ j i,hji]
    simp
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    simp only [P.root_reflectionPerm,P.reflection_apply,map_sub,map_smul,
      P.root_coroot'_eq_pairing,P.pairing_same,hpij,hpji]
    module

end Atlas.Chevalley.RootData
