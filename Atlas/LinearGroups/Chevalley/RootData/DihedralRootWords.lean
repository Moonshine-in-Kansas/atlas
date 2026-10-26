import Atlas.LinearGroups.Chevalley.RootData.RootStringReflectionTransport
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Module

/-! Source candidate: finite integral reflection-word identities. The words
and inversion-root lists are explicit; no Coxeter presentation is supplied. -/

noncomputable section
namespace Atlas.Chevalley.RootData
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]

def reflectionWord : List ι → Equiv.Perm ι
  | [] => 1
  | i :: l => P.reflectionPerm i * reflectionWord l

/-- Roots indexing the scalar factors in a left-written Weyl word. The inverse
suffix appears because coefficients are transported from the acted-on root. -/
def inversionRoots : List ι → List ι
  | [] => []
  | i :: l => (reflectionWord P l)⁻¹ i :: inversionRoots l

theorem chainBotCoeff_reflectionWord_right (l : List ι) (i j : ι) :
    P.chainBotCoeff i (reflectionWord P l j) =
      P.chainBotCoeff ((reflectionWord P l)⁻¹ i) j := by
  induction l generalizing i with
  | nil => simp [reflectionWord]
  | cons k l ih =>
    simp only [reflectionWord, mul_inv_rev, Equiv.Perm.mul_apply,
      P.reflectionPerm_inv]
    rw [chainBotCoeff_reflection_right, ih]

theorem reflectionWord_four (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    reflectionWord P [i, j, i, j] = reflectionWord P [j, i, j, i] := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij]
    simp
  have hpji : P.pairing j i = -2 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji]
    simp
  ext k
  apply P.root.injective
  simp only [reflectionWord, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
    P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
  module

theorem reflectionWord_six (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3) :
    reflectionWord P [i, j, i, j, i, j] =
      reflectionWord P [j, i, j, i, j, i] := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij]
    simp
  have hpji : P.pairing j i = -3 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji]
    simp
  ext k
  apply P.root.injective
  simp only [reflectionWord, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
    P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
  module

theorem inversionRoots_four_reverse (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -2) :
    inversionRoots P [i, j, i, j] = (inversionRoots P [j, i, j, i]).reverse := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij]
    simp
  have hpji : P.pairing j i = -2 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji]
    simp
  simp only [inversionRoots, reflectionWord, mul_inv_rev, inv_one,
    P.reflectionPerm_inv, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module

theorem inversionRoots_six_reverse (i j : ι)
    (hij : P.pairingIn ℤ i j = -1) (hji : P.pairingIn ℤ j i = -3) :
    inversionRoots P [i, j, i, j, i, j] =
      (inversionRoots P [j, i, j, i, j, i]).reverse := by
  have hpij : P.pairing i j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i j, hij]
    simp
  have hpji : P.pairing j i = -3 := by
    rw [← P.algebraMap_pairingIn ℤ j i, hji]
    simp
  simp only [inversionRoots, reflectionWord, mul_inv_rev, inv_one,
    P.reflectionPerm_inv, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module

end Atlas.Chevalley.RootData
