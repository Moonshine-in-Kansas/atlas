import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Atlas.LinearGroups.Chevalley.RootData.RootHeightCombination
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength
import Mathlib.Tactic.Module

/-! Actual two-descent suffixes of lengths two and three. Each length drop
follows from an explicit positive root combination and the checked sign
criterion for minimal length, without any Coxeter-system premise. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Nonnegative, nonzero combinations retain negative images under an actual
Weyl-image element. The proof uses its actual simple-reflection word. -/
theorem rootWeyl_not_isPos_of_combination
    (w : P.weylGroupToPerm.range) (i j k : ι) (a c : ℤ)
    (hk : P.root k = a • P.root i + c • P.root j)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : 0 < a + c)
    (hi : ¬ b.IsPos (w.val i)) (hj : ¬ b.IsPos (w.val j)) :
    ¬ b.IsPos (w.val k) := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b w.property
  have hi' : ¬ b.IsPos (simpleReflectionWord P b l i) := by
    simpa only [hl] using hi
  have hj' : ¬ b.IsPos (simpleReflectionWord P b l j) := by
    simpa only [hl] using hj
  simpa only [hl] using simpleReflectionWord_not_isPos_of_combination P b
    l i j k a c hk ha hc hac hi' hj'

/-- Two negative simple-root images force 2 successive exact descents. -/
theorem rootWeylLength_two_descents_two
    (w : P.weylGroupToPerm.range) (i j : b.support)
    (hij : b.cartanMatrix i j = 0) (hji : b.cartanMatrix j i = 0)
    (hi : ¬ b.IsPos (w.val i.val)) (hj : ¬ b.IsPos (w.val j.val)) :
    let s := simpleWeylReflection P b
    rootWeylLength P b (w * s i * s j) + 2 = rootWeylLength P b w := by
  let s := simpleWeylReflection P b
  have hbij : P.pairingIn ℤ i.val j.val = 0 := hij
  have hbji : P.pairingIn ℤ j.val i.val = 0 := hji
  have hpij : P.pairing i.val j.val = 0 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, hbij]
    simp
  have hpji : P.pairing j.val i.val = 0 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, hbji]
    simp
  have hdrop0 := rootWeylLength_mul_simple_of_negative P b w i hi
  have hroot1 : P.root (P.reflectionPerm i.val (j.val)) =
      (0 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg1 : ¬ b.IsPos ((w * s i).val j.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (j.val)))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (j.val)) 0 1 hroot1
      (by decide) (by decide) (by decide) hi hj
  have hdrop1 := rootWeylLength_mul_simple_of_negative P b
    (w * s i) j hneg1
  change rootWeylLength P b (w * s i * s j) + 2 = rootWeylLength P b w
  dsimp only [s] at *
  omega

/-- Two negative simple-root images force 3 successive exact descents. -/
theorem rootWeylLength_two_descents_three
    (w : P.weylGroupToPerm.range) (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1)
    (hi : ¬ b.IsPos (w.val i.val)) (hj : ¬ b.IsPos (w.val j.val)) :
    let s := simpleWeylReflection P b
    rootWeylLength P b (w * s i * s j * s i) + 3 = rootWeylLength P b w := by
  let s := simpleWeylReflection P b
  have hbij : P.pairingIn ℤ i.val j.val = -1 := hij
  have hbji : P.pairingIn ℤ j.val i.val = -1 := hji
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, hbij]
    simp
  have hpji : P.pairing j.val i.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, hbji]
    simp
  have hdrop0 := rootWeylLength_mul_simple_of_negative P b w i hi
  have hroot1 : P.root (P.reflectionPerm i.val (j.val)) =
      (1 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg1 : ¬ b.IsPos ((w * s i).val j.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (j.val)))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (j.val)) 1 1 hroot1
      (by decide) (by decide) (by decide) hi hj
  have hdrop1 := rootWeylLength_mul_simple_of_negative P b
    (w * s i) j hneg1
  have hroot2 : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))) =
      (0 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg2 : ¬ b.IsPos ((w * s i * s j).val i.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))) 0 1 hroot2
      (by decide) (by decide) (by decide) hi hj
  have hdrop2 := rootWeylLength_mul_simple_of_negative P b
    (w * s i * s j) i hneg2
  change rootWeylLength P b (w * s i * s j * s i) + 3 = rootWeylLength P b w
  dsimp only [s] at *
  omega

end Atlas.Chevalley.RootData
