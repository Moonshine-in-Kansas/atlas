import Atlas.LinearGroups.Chevalley.RootData.PositiveIntegralRootCone
import Mathlib.Tactic.Module

/-! Literal A2/B2 root labels and the cones on the original commutator
inputs. These root calculations do not assume ambient simple roots. -/
noncomputable section
namespace Atlas.Chevalley.RootData

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]

/-- The chosen A2 family n_i X_j has root α+β. -/
theorem a2_literal_root_label (i j : ι)
    (hji : P.pairingIn ℤ j i = -1) :
    P.root (P.reflectionPerm i j) = (1 : ℤ) • P.root i + (1 : ℤ) • P.root j := by
  have hpji : P.pairing j i = -1 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji]
    simp
  simp only [P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing, hpji]
  module

/-- The chosen B2 families n_j X_i and n_i X_j have roots α+β and 2α+β. -/
theorem b2_literal_root_labels (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    P.root (P.reflectionPerm j i) = (1 : ℤ) • P.root i + (1 : ℤ) • P.root j ∧
    P.root (P.reflectionPerm i j) = (2 : ℤ) • P.root i + (1 : ℤ) • P.root j := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij]
    simp
  have hpji : P.pairing j i = -2 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji]
    simp
  constructor
  all_goals
    simp only [P.root_reflectionPerm, P.reflection_apply,
      P.root_coroot'_eq_pairing, hpij, hpji]
    module

/-- The only output in the complete A2 commutator table is in the positive
integral cone on the two original input labels. -/
theorem a2_literal_commutator_root_cone (b : P.Base) (i j : ι)
    (hji : P.pairingIn ℤ j i = -1) :
    PositiveIntegralRootCone P b i j (P.reflectionPerm i j) :=
  positiveIntegralRootCone_of_root_eq P b i j (P.reflectionPerm i j)
    1 1 (by decide) (by decide) (a2_literal_root_label P i j hji)

/-- The two mixed outputs and the short--short output each lie in the cone
on that pair's original labels. No assertion is made just from total height. -/
theorem b2_literal_commutator_root_cones (b : P.Base) (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    let z := P.reflectionPerm j i
    let v := P.reflectionPerm i j
    PositiveIntegralRootCone P b i j z ∧ PositiveIntegralRootCone P b i j v ∧
    PositiveIntegralRootCone P b i z v := by
  obtain ⟨hz, hv⟩ := b2_literal_root_labels P i j hij hji
  refine ⟨?_, ?_, ?_⟩
  · exact positiveIntegralRootCone_of_root_eq P b i j (P.reflectionPerm j i)
      1 1 (by decide) (by decide) hz
  · exact positiveIntegralRootCone_of_root_eq P b i j (P.reflectionPerm i j)
      2 1 (by decide) (by decide) hv
  · apply positiveIntegralRootCone_of_root_eq P b i (P.reflectionPerm j i)
      (P.reflectionPerm i j) 1 1 (by decide) (by decide)
    rw [hz, hv]
    module

end Atlas.Chevalley.RootData
