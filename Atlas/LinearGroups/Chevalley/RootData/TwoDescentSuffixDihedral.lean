import Atlas.LinearGroups.Chevalley.RootData.TwoDescentSuffix

/-! Actual two-descent suffixes of lengths four and six, with i the short
simple root. Integral positive-combination identities imply every successive
descent; no assumed rank-two length or Coxeter presentation is used. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Two negative simple-root images force 4 successive exact descents. -/
theorem rootWeylLength_two_descents_four
    (w : P.weylGroupToPerm.range) (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2)
    (hi : ¬ b.IsPos (w.val i.val)) (hj : ¬ b.IsPos (w.val j.val)) :
    let s := simpleWeylReflection P b
    rootWeylLength P b (w * s i * s j * s i * s j) + 4 = rootWeylLength P b w := by
  let s := simpleWeylReflection P b
  have hbij : P.pairingIn ℤ i.val j.val = -1 := hij
  have hbji : P.pairingIn ℤ j.val i.val = -2 := hji
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, hbij]
    simp
  have hpji : P.pairing j.val i.val = -2 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, hbji]
    simp
  have hdrop0 := rootWeylLength_mul_simple_of_negative P b w i hi
  have hroot1 : P.root (P.reflectionPerm i.val (j.val)) =
      (2 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg1 : ¬ b.IsPos ((w * s i).val j.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (j.val)))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (j.val)) 2 1 hroot1
      (by decide) (by decide) (by decide) hi hj
  have hdrop1 := rootWeylLength_mul_simple_of_negative P b
    (w * s i) j hneg1
  have hroot2 : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))) =
      (1 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg2 : ¬ b.IsPos ((w * s i * s j).val i.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))) 1 1 hroot2
      (by decide) (by decide) (by decide) hi hj
  have hdrop2 := rootWeylLength_mul_simple_of_negative P b
    (w * s i * s j) i hneg2
  have hroot3 : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))) =
      (0 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg3 : ¬ b.IsPos ((w * s i * s j * s i).val j.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))) 0 1 hroot3
      (by decide) (by decide) (by decide) hi hj
  have hdrop3 := rootWeylLength_mul_simple_of_negative P b
    (w * s i * s j * s i) j hneg3
  change rootWeylLength P b (w * s i * s j * s i * s j) + 4 = rootWeylLength P b w
  dsimp only [s] at *
  omega

/-- Two negative simple-root images force 6 successive exact descents. -/
theorem rootWeylLength_two_descents_six
    (w : P.weylGroupToPerm.range) (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (hi : ¬ b.IsPos (w.val i.val)) (hj : ¬ b.IsPos (w.val j.val)) :
    let s := simpleWeylReflection P b
    rootWeylLength P b (w * s i * s j * s i * s j * s i * s j) + 6 = rootWeylLength P b w := by
  let s := simpleWeylReflection P b
  have hbij : P.pairingIn ℤ i.val j.val = -1 := hij
  have hbji : P.pairingIn ℤ j.val i.val = -3 := hji
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, hbij]
    simp
  have hpji : P.pairing j.val i.val = -3 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, hbji]
    simp
  have hdrop0 := rootWeylLength_mul_simple_of_negative P b w i hi
  have hroot1 : P.root (P.reflectionPerm i.val (j.val)) =
      (3 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg1 : ¬ b.IsPos ((w * s i).val j.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (j.val)))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (j.val)) 3 1 hroot1
      (by decide) (by decide) (by decide) hi hj
  have hdrop1 := rootWeylLength_mul_simple_of_negative P b
    (w * s i) j hneg1
  have hroot2 : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))) =
      (2 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg2 : ¬ b.IsPos ((w * s i * s j).val i.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))) 2 1 hroot2
      (by decide) (by decide) (by decide) hi hj
  have hdrop2 := rootWeylLength_mul_simple_of_negative P b
    (w * s i * s j) i hneg2
  have hroot3 : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))) =
      (3 : ℤ) • P.root i.val + (2 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg3 : ¬ b.IsPos ((w * s i * s j * s i).val j.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))) 3 2 hroot3
      (by decide) (by decide) (by decide) hi hj
  have hdrop3 := rootWeylLength_mul_simple_of_negative P b
    (w * s i * s j * s i) j hneg3
  have hroot4 : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))))) =
      (1 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg4 : ¬ b.IsPos ((w * s i * s j * s i * s j).val i.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))))))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val (i.val))))) 1 1 hroot4
      (by decide) (by decide) (by decide) hi hj
  have hdrop4 := rootWeylLength_mul_simple_of_negative P b
    (w * s i * s j * s i * s j) i hneg4
  have hroot5 : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))))) =
      (0 : ℤ) • P.root i.val + (1 : ℤ) • P.root j.val := by
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  have hneg5 : ¬ b.IsPos ((w * s i * s j * s i * s j * s i).val j.val) := by
    change ¬ b.IsPos (w.val (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))))))
    exact rootWeyl_not_isPos_of_combination P b w i.val j.val
      (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val (P.reflectionPerm i.val (j.val)))))) 0 1 hroot5
      (by decide) (by decide) (by decide) hi hj
  have hdrop5 := rootWeylLength_mul_simple_of_negative P b
    (w * s i * s j * s i * s j * s i) j hneg5
  change rootWeylLength P b (w * s i * s j * s i * s j * s i * s j) + 6 = rootWeylLength P b w
  dsimp only [s] at *
  omega

end Atlas.Chevalley.RootData
