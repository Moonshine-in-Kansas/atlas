import Atlas.LinearGroups.Chevalley.WeightCompanionRootMarks
import Atlas.LinearGroups.Chevalley.WeightCompanionA2Transport
import Atlas.LinearGroups.Chevalley.WeightCompanionZeroCartanNormalization
import Mathlib.Tactic.Module

/-! Zero-edge and A2 marked braid sets, on the same literal label/subgroup
interface as B2. The conclusions compare actual subgroups, and no arbitrary
choice of a root subgroup is identified in their hypotheses. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Integral Integral.Minuscule Atlas.GroupTheory Atlas.GroupTheory.ReducedWords

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

include hdiamond

theorem weightCompanionRootMark_fixed_of_zero_cartan
    (i j : b.support) (hne : i ≠ j) (hji : b.cartanMatrix j i = 0) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
      (weightCompanionSimpleRootMark P b O hc hm R j) =
      weightCompanionSimpleRootMark P b O hc hm R j := by
  apply Prod.ext
  · have hpji : P.pairing j.val i.val = 0 := by
      rw [← P.algebraMap_pairingIn ℤ j.val i.val,
        show P.pairingIn ℤ j.val i.val = 0 from hji]
      simp
    change P.reflectionPerm i.val j.val = j.val
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply,
      P.root_coroot'_eq_pairing, hpji, zero_smul, sub_zero]
  · apply conjugateSubgroup_range_eq_of_surjective _ _ _ id Function.surjective_id
    intro x
    exact weightCompanionWeyl_conjugate_X_of_zero_cartan
      P b hdiamond O hc hm R i j hne hji 1 x.toAdd

theorem weightCompanionRootMark_a2_swap
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
      (weightCompanionSimpleRootMark P b O hc hm R j) =
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
      (weightCompanionSimpleRootMark P b O hc hm R i) := by
  apply Prod.ext
  · have hpij : P.pairing i.val j.val = -1 := by
      rw [← P.algebraMap_pairingIn ℤ i.val j.val,
        show P.pairingIn ℤ i.val j.val = -1 from hij]
      simp
    have hpji : P.pairing j.val i.val = -1 := by
      rw [← P.algebraMap_pairingIn ℤ j.val i.val,
        show P.pairingIn ℤ j.val i.val = -1 from hji]
      simp
    change P.reflectionPerm i.val j.val = P.reflectionPerm j.val i.val
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply,
      P.root_coroot'_eq_pairing, hpij, hpji]
    module
  · let nj := weightCompanionWeyl P b O hc hm R j 1
    let f := (MulAut.conj nj).toMonoidHom.comp (weightCompanionXHom P b O hc hm R i)
    have h : conjugateSubgroup (weightCompanionWeyl P b O hc hm R i 1)
        (weightCompanionXHom P b O hc hm R j).range = f.range := by
      apply conjugateSubgroup_range_eq_of_surjective _ _ _ Inv.inv inv_surjective
      intro x
      exact weightCompanionWeyl_a2_X_swap_conjugate
        P b hdiamond O hc hm R j i hne.symm hji hij x.toAdd
    change conjugateSubgroup (weightCompanionWeyl P b O hc hm R i 1)
      (weightCompanionXHom P b O hc hm R j).range =
      conjugateSubgroup nj (weightCompanionXHom P b O hc hm R i).range
    simpa only [conjugateSubgroup_range, f] using h

theorem weightCompanionRootMark_a2_transport
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R i)
      (labelledSubgroupAction (weightCompanionMarkedWeyl P b O hc hm R j)
        (weightCompanionSimpleRootMark P b O hc hm R i)) =
      weightCompanionSimpleRootMark P b O hc hm R j := by
  apply Prod.ext
  · have hpij : P.pairing i.val j.val = -1 := by
      rw [← P.algebraMap_pairingIn ℤ i.val j.val,
        show P.pairingIn ℤ i.val j.val = -1 from hij]
      simp
    have hpji : P.pairing j.val i.val = -1 := by
      rw [← P.algebraMap_pairingIn ℤ j.val i.val,
        show P.pairingIn ℤ j.val i.val = -1 from hji]
      simp
    change P.reflectionPerm i.val (P.reflectionPerm j.val i.val) = j.val
    apply P.root.injective
    simp only [P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
      P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
    module
  · change conjugateSubgroup (weightCompanionWeyl P b O hc hm R i 1)
      (conjugateSubgroup (weightCompanionWeyl P b O hc hm R j 1)
        (weightCompanionXHom P b O hc hm R i).range) =
          (weightCompanionXHom P b O hc hm R j).range
    rw [← conjugateSubgroup_mul]
    apply conjugateSubgroup_range_eq_of_surjective _ _ _ id Function.surjective_id
    intro x
    exact weightCompanionWeyl_a2_transport_X
      P b hdiamond O hc hm R i j hne hij hji x.toAdd

theorem weightCompanionMarkedWordSet_zero
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = 0) (hji : b.cartanMatrix j i = 0) :
    weightCompanionMarkedWordSet P b O hc hm R [i,j] =
      weightCompanionMarkedWordSet P b O hc hm R [j,i] := by
  apply markedWordSet_two_of_fixed
  · exact weightCompanionRootMark_fixed_of_zero_cartan P b hdiamond O hc hm R i j hne hji
  · exact weightCompanionRootMark_fixed_of_zero_cartan P b hdiamond O hc hm R j i hne.symm hij

theorem weightCompanionMarkedWordSet_a2
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    weightCompanionMarkedWordSet P b O hc hm R [i,j,i] =
      weightCompanionMarkedWordSet P b O hc hm R [j,i,j] := by
  apply markedWordSet_three_of_transport
  · exact weightCompanionRootMark_a2_swap P b hdiamond O hc hm R i j hne hij hji
  · exact weightCompanionRootMark_a2_transport P b hdiamond O hc hm R i j hne hij hji
  · exact weightCompanionRootMark_a2_transport P b hdiamond O hc hm R j i hne.symm hji hij

end Atlas.Chevalley
