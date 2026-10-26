import Atlas.LinearGroups.Chevalley.RootData.ParabolicWordReduction
import Atlas.LinearGroups.Chevalley.RootData.SupportedRootWordLabels
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Tactic.Ring

/-! Outside-node coefficients detect a conjugated adjacent reflection outside
an actual root parabolic. All calculations occur in the integral root lattice. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem rootSimpleCoefficient_reflection_of_ne
    (i j : b.support) (hij : i ≠ j) (β : ι) :
    rootSimpleCoefficients P b (P.reflectionPerm i.val β) j =
      rootSimpleCoefficients P b β j := by
  simp only [rootSimpleCoefficients_reflection, Finsupp.sub_apply,
    Finsupp.smul_apply, Finsupp.single_apply, if_neg hij, smul_zero, sub_zero]

theorem rootParabolic_preserves_outside_simpleCoefficient
    (J : Finset b.support) (j : b.support) (hj : j ∉ J)
    (w : P.weylGroupToPerm.range) (hw : w ∈ rootParabolicSubgroup P b J)
    (β : ι) :
    rootSimpleCoefficients P b (w.val β) j = rootSimpleCoefficients P b β j := by
  obtain ⟨l, hl, rfl⟩ := (rootParabolic_mem_iff_word P b J w).mp hw
  clear hw
  induction l generalizing β with
  | nil => rfl
  | cons i l ih =>
    have hij : i ≠ j := by
      intro he
      exact hj (he ▸ hl i List.mem_cons_self)
    change rootSimpleCoefficients P b
      (P.reflectionPerm i.val ((rootWeylWord P b l).val β)) j = _
    rw [rootSimpleCoefficient_reflection_of_ne P b i j hij]
    exact ih β (fun k hk => hl k (List.mem_cons_of_mem i hk))

private theorem pairingIn_reflection_left (i β k : ι) :
    P.pairingIn ℤ (P.reflectionPerm i β) k =
      P.pairingIn ℤ β k - P.pairingIn ℤ β i * P.pairingIn ℤ i k := by
  apply FaithfulSMul.algebraMap_injective ℤ ℤ
  simp only [map_sub, map_mul, P.algebraMap_pairingIn]
  rw [← P.root_coroot'_eq_pairing k (P.reflectionPerm i β),
    P.root_reflectionPerm, P.reflection_apply]
  simp only [map_sub, map_smul, P.root_coroot'_eq_pairing, smul_eq_mul]

theorem simple_adjacent_double_reflection_isPos
    (i j : b.support) (hij : i ≠ j) (hji : b.cartanMatrix j i ≠ 0) :
    b.IsPos (P.reflectionPerm j.val (P.reflectionPerm i.val j.val)) := by
  have hval : j.val ≠ i.val := fun he => hij (Subtype.ext he.symm)
  have hp := (b.isPos_of_mem_support j.property).reflectionPerm i.property hval
  apply hp.reflectionPerm j.property
  intro he
  have hec := congrArg (fun β => rootSimpleCoefficients P b β i) he
  simp only [rootSimpleCoefficients_reflection, rootSimpleCoefficients_simple,
    Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply,
    if_neg hij.symm, ite_true, smul_eq_mul, zero_sub, mul_one] at hec
  change -b.cartanMatrix j i = 0 at hec
  exact hji (neg_eq_zero.mp hec)

theorem rootSimpleCoefficient_conjugated_simple
    (i j : b.support) (hij : i ≠ j) :
    rootSimpleCoefficients P b
      (P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val j.val))) j =
      1 - b.cartanMatrix i j * b.cartanMatrix j i := by
  simp only [rootSimpleCoefficients_reflection, rootSimpleCoefficients_simple,
    Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply,
    ite_true, if_neg hij, smul_eq_mul, pairingIn_reflection_left,
    P.pairingIn_same]
  change _ = 1 - P.pairingIn ℤ i.val j.val * P.pairingIn ℤ j.val i.val
  ring

theorem conjugated_adjacent_simple_not_mem_rootParabolic
    (J : Finset b.support) (i j : b.support) (hj : j ∉ J)
    (hij : i ≠ j) (hcartan : b.cartanMatrix i j ≠ 0) :
    simpleWeylReflection P b j * simpleWeylReflection P b i *
        simpleWeylReflection P b j ∉ rootParabolicSubgroup P b J := by
  intro hw
  have he := rootParabolic_preserves_outside_simpleCoefficient P b J j hj _ hw j.val
  change rootSimpleCoefficients P b
    (P.reflectionPerm j.val (P.reflectionPerm i.val (P.reflectionPerm j.val j.val))) j =
      rootSimpleCoefficients P b j.val j at he
  rw [rootSimpleCoefficient_conjugated_simple P b i j hij,
    rootSimpleCoefficients_simple, Finsupp.single_eq_same] at he
  have hji : b.cartanMatrix j i ≠ 0 := by
    intro hz
    exact hcartan (b.cartanMatrix_apply_eq_zero_iff_symm.mpr hz)
  exact (mul_ne_zero hcartan hji) (by omega)

end Atlas.Chevalley.RootData
