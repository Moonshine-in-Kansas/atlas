import Atlas.GroupTheory.RootFamilyCommutators
import Atlas.LinearGroups.Chevalley.PositiveRootConeSubgroup
import Atlas.LinearGroups.Chevalley.LiteralPositiveRootRanges
import Atlas.LinearGroups.Chevalley.WeightCompanionTripleEdgeCommutator
import Atlas.LinearGroups.Chevalley.WeightCompanionG2PositivePairCommutators
import Atlas.LinearGroups.Chevalley.RootData.G2CommutatorRootCones
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The complete six-root local G2 table yields actual canonical positive-root
subgroup containment in the original pair's positive integral cone. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
open scoped commutatorElement
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]
  (hdiamond : SimpleDiamondProducts P b)
include hdiamond

set_option maxHeartbeats 2000000 in
/-- All ordered pairs in the six literal positive roots of a saturated G2
simple pair. The 120-degree short pair uses its actual three-factor formula. -/
theorem positiveRootSubgroup_g2_local_cone
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (α β : {γ : ι // b.IsPos γ})
    (hα : α.val = i.val ∨ α.val = j.val ∨ α.val = P.reflectionPerm j.val i.val ∨
      α.val = P.reflectionPerm i.val (P.reflectionPerm j.val i.val) ∨
      α.val = P.reflectionPerm i.val j.val ∨
      α.val = P.reflectionPerm j.val (P.reflectionPerm i.val j.val))
    (hβ : β.val = i.val ∨ β.val = j.val ∨ β.val = P.reflectionPerm j.val i.val ∨
      β.val = P.reflectionPerm i.val (P.reflectionPerm j.val i.val) ∨
      β.val = P.reflectionPerm i.val j.val ∨
      β.val = P.reflectionPerm j.val (P.reflectionPerm i.val j.val)) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
  let ni := weightCompanionWeyl P b O hc hm R i 1
  let nj := weightCompanionWeyl P b O hc hm R j 1
  let X := weightCompanionXHom P b O hc hm R i
  let Y := weightCompanionXHom P b O hc hm R j
  let Z := (MulAut.conj nj).toMonoidHom.comp X
  let W := (MulAut.conj (ni * nj)).toMonoidHom.comp X
  let V := (MulAut.conj ni).toMonoidHom.comp Y
  let H := (MulAut.conj (nj * ni)).toMonoidHom.comp Y
  have hxval (a : R) : X (Multiplicative.ofAdd a) =
      weightCompanionX P b O hc hm R i a := rfl
  have hyval (a : R) : Y (Multiplicative.ofAdd a) =
      weightCompanionX P b O hc hm R j a := rfl
  have hzval (a : R) : Z (Multiplicative.ofAdd a) =
      nj * weightCompanionX P b O hc hm R i a * nj⁻¹ := by
    simp only [Z, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hxval]
  have hwval (a : R) : W (Multiplicative.ofAdd a) =
      (ni * nj) * weightCompanionX P b O hc hm R i a * (ni * nj)⁻¹ := by
    simp only [W, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hxval]
  have hvval (a : R) : V (Multiplicative.ofAdd a) =
      ni * weightCompanionX P b O hc hm R j a * ni⁻¹ := by
    simp only [V, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hyval]
  have hhval (a : R) : H (Multiplicative.ofAdd a) =
      (nj * ni) * weightCompanionX P b O hc hm R j a * (nj * ni)⁻¹ := by
    simp only [H, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hyval]
  have hxy (s t : R) :
      ⁅X (Multiplicative.ofAdd s), Y (Multiplicative.ofAdd t)⁆ =
        Z (Multiplicative.ofAdd (-s*t)) * W (Multiplicative.ofAdd (s^2*t)) *
          V (Multiplicative.ofAdd (s^3*t)) * H (Multiplicative.ofAdd (2*s^3*t^2)) := by
    rw [hxval, hyval, hzval, hwval, hvval, hhval]
    simpa only [ni, nj] using
      weightCompanionX_g2_commutator_eq_weyl_product P b hdiamond O hc hm R i j hne hij hji s t
  have hxz (s t : R) :
      ⁅X (Multiplicative.ofAdd s), Z (Multiplicative.ofAdd t)⁆ =
        W (Multiplicative.ofAdd (-2*s*t)) * V (Multiplicative.ofAdd (-3*s^2*t)) *
          H (Multiplicative.ofAdd (-3*s*t^2)) := by
    rw [hxval, hzval, hwval, hvval, hhval]
    simpa only [ni, nj] using
      weightCompanionX_g2_short_pair_commutator P b hdiamond O hc hm R i j hne hij hji s t
  have hxw (s t : R) :
      ⁅X (Multiplicative.ofAdd s), W (Multiplicative.ofAdd t)⁆ =
        V (Multiplicative.ofAdd (3*s*t)) := by
    rw [hxval, hwval, hvval]
    simpa only [ni, nj] using
      (weightCompanion_g2_positive_pairs_twoStep_and_commute
        P b hdiamond O hc hm R i j hne hij hji s t).1
  have hyv (s t : R) :
      ⁅Y (Multiplicative.ofAdd s), V (Multiplicative.ofAdd t)⁆ =
        H (Multiplicative.ofAdd (s*t)) := by
    rw [hyval, hvval, hhval]
    simpa only [ni, nj] using
      (weightCompanion_g2_positive_pairs_twoStep_and_commute
        P b hdiamond O hc hm R i j hne hij hji s t).2.1
  have hzw (s t : R) :
      ⁅Z (Multiplicative.ofAdd s), W (Multiplicative.ofAdd t)⁆ =
        H (Multiplicative.ofAdd (3*s*t)) := by
    rw [hzval, hwval, hhval]
    simpa only [ni, nj] using
      (weightCompanion_g2_positive_pairs_twoStep_and_commute
        P b hdiamond O hc hm R i j hne hij hji s t).2.2.1
  let F : Fin 6 → (Multiplicative R →* WeightCompanion P b O hc hm R) := ![X, Y, Z, W, V, H]
  let label : Fin 6 → ι := ![i.val, j.val, P.reflectionPerm j.val i.val,
    P.reflectionPerm i.val (P.reflectionPerm j.val i.val),
    P.reflectionPerm i.val j.val, P.reflectionPerm j.val (P.reflectionPerm i.val j.val)]
  let K := fun a c : Fin 6 => positiveWeightCompanionConeSubgroup P b O hc hm R (label a) (label c)
  have hrange (a : Fin 6) (γ : {γ : ι // b.IsPos γ}) (ha : label a = γ.val) :
      (F a).range = positiveWeightCompanionRootSubgroup P b O hc hm R γ := by
    fin_cases a
    · exact (weightCompanionXHom_range_eq_positiveRoot P b O hc hm R hdiamond i).trans
        (congrArg (positiveWeightCompanionRootSubgroup P b O hc hm R) (Subtype.ext ha))
    · exact (weightCompanionXHom_range_eq_positiveRoot P b O hc hm R hdiamond j).trans
        (congrArg (positiveWeightCompanionRootSubgroup P b O hc hm R) (Subtype.ext ha))
    · apply weightCompanion_conjugateXHom_range_eq_positiveRoot
        P b O hc hm R hdiamond (weightCompanionSimpleWeylInN P b O hc hm R j) i γ.val γ.property
      rw [weightCompanionNRootPermHom_simple]
      exact ha
    · apply weightCompanion_conjugateXHom_range_eq_positiveRoot
        P b O hc hm R hdiamond
          (weightCompanionSimpleWeylInN P b O hc hm R i *
            weightCompanionSimpleWeylInN P b O hc hm R j) i γ.val γ.property
      rw [map_mul, weightCompanionNRootPermHom_simple, weightCompanionNRootPermHom_simple]
      exact ha
    · apply weightCompanion_conjugateXHom_range_eq_positiveRoot
        P b O hc hm R hdiamond (weightCompanionSimpleWeylInN P b O hc hm R i) j γ.val γ.property
      rw [weightCompanionNRootPermHom_simple]
      exact ha
    · apply weightCompanion_conjugateXHom_range_eq_positiveRoot
        P b O hc hm R hdiamond
          (weightCompanionSimpleWeylInN P b O hc hm R j *
            weightCompanionSimpleWeylInN P b O hc hm R i) j γ.val γ.property
      rw [map_mul, weightCompanionNRootPermHom_simple, weightCompanionNRootPermHom_simple]
      exact ha
  obtain ⟨hz, hw, hv, hh, hazw, hazv, hazh, hawv, hbvh, hzwh⟩ :=
    g2_literal_commutator_root_cones P b i.val j.val hij hji
  have hipos := b.isPos_of_mem_support i.property
  have hjpos := b.isPos_of_mem_support j.property
  have hpos (a : Fin 6) : b.IsPos (label a) := by
    fin_cases a
    · exact hipos
    · exact hjpos
    · exact positiveIntegralRootCone_isPos P b hz hipos hjpos
    · exact positiveIntegralRootCone_isPos P b hw hipos hjpos
    · exact positiveIntegralRootCone_isPos P b hv hipos hjpos
    · exact positiveIntegralRootCone_isPos P b hh hipos hjpos
  have hout (a c k : Fin 6)
      (hk : PositiveIntegralRootCone P b (label a) (label c) (label k))
      (t : R) : F k (Multiplicative.ofAdd t) ∈ K a c := by
    apply positiveWeightCompanionRootSubgroup_le_cone P b O hc hm R
      (label a) (label c) ⟨label k, hpos k⟩ hk
    rw [← hrange k ⟨label k, hpos k⟩ rfl]
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  have h01 : ⁅(F 0).range, (F 1).range⁆ ≤ K 0 1 := by
    apply rootRange_commutator_le X Y (K 0 1)
    intro s t
    rw [hxy]
    have hz' := hout 0 1 2 hz (-s*t)
    have hw' := hout 0 1 3 hw (s^2*t)
    have hv' := hout 0 1 4 hv (s^3*t)
    have hh' := hout 0 1 5 hh (2*s^3*t^2)
    rw [show F 2 = Z from rfl] at hz'
    rw [show F 3 = W from rfl] at hw'
    rw [show F 4 = V from rfl] at hv'
    rw [show F 5 = H from rfl] at hh'
    exact (K 0 1).mul_mem ((K 0 1).mul_mem ((K 0 1).mul_mem hz' hw') hv') hh'
  have h02 : ⁅(F 0).range, (F 2).range⁆ ≤ K 0 2 := by
    apply rootRange_commutator_le X Z (K 0 2)
    intro s t
    rw [hxz]
    have hw' := hout 0 2 3 hazw (-2*s*t)
    have hv' := hout 0 2 4 hazv (-3*s^2*t)
    have hh' := hout 0 2 5 hazh (-3*s*t^2)
    rw [show F 3 = W from rfl] at hw'
    rw [show F 4 = V from rfl] at hv'
    rw [show F 5 = H from rfl] at hh'
    exact (K 0 2).mul_mem ((K 0 2).mul_mem hw' hv') hh'
  have h03 : ⁅(F 0).range, (F 3).range⁆ ≤ K 0 3 := by
    apply rootRange_commutator_le X W (K 0 3)
    intro s t
    rw [hxw]
    have hv' := hout 0 3 4 hawv (3*s*t)
    rw [show F 4 = V from rfl] at hv'
    exact hv'
  have h14 : ⁅(F 1).range, (F 4).range⁆ ≤ K 1 4 := by
    apply rootRange_commutator_le Y V (K 1 4)
    intro s t
    rw [hyv]
    have hh' := hout 1 4 5 hbvh (s*t)
    rw [show F 5 = H from rfl] at hh'
    exact hh'
  have h23 : ⁅(F 2).range, (F 3).range⁆ ≤ K 2 3 := by
    apply rootRange_commutator_le Z W (K 2 3)
    intro s t
    rw [hzw]
    have hh' := hout 2 3 5 hzwh (3*s*t)
    rw [show F 5 = H from rfl] at hh'
    exact hh'
  have h04 : ⁅(F 0).range, (F 4).range⁆ ≤ K 0 4 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, hpair, _, _, _, _, _, _, _, _, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h05 : ⁅(F 0).range, (F 5).range⁆ ≤ K 0 5 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, hpair, _, _, _, _, _, _, _, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h12 : ⁅(F 1).range, (F 2).range⁆ ≤ K 1 2 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, _, hpair, _, _, _, _, _, _, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h13 : ⁅(F 1).range, (F 3).range⁆ ≤ K 1 3 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, _, _, hpair, _, _, _, _, _, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h15 : ⁅(F 1).range, (F 5).range⁆ ≤ K 1 5 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, _, _, _, hpair, _, _, _, _, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h24 : ⁅(F 2).range, (F 4).range⁆ ≤ K 2 4 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, _, _, _, _, hpair, _, _, _, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h25 : ⁅(F 2).range, (F 5).range⁆ ≤ K 2 5 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, _, _, _, _, _, hpair, _, _, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h34 : ⁅(F 3).range, (F 4).range⁆ ≤ K 3 4 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hpair, _, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h35 : ⁅(F 3).range, (F 5).range⁆ ≤ K 3 5 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpair, _⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have h45 : ⁅(F 4).range, (F 5).range⁆ ≤ K 4 5 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hpair⟩ := weightCompanion_g2_positive_pairs_twoStep_and_commute
      P b hdiamond O hc hm R i j hne hij hji s t
    exact hpair
  have hreverse (a c : Fin 6) (h : ⁅(F a).range, (F c).range⁆ ≤ K a c) :
      ⁅(F c).range, (F a).range⁆ ≤ K c a := by
    change _ ≤ positiveWeightCompanionConeSubgroup P b O hc hm R (label c) (label a)
    rw [Subgroup.commutator_comm,
      positiveWeightCompanionConeSubgroup_comm P b O hc hm R (label c) (label a)]
    exact h
  have hlocal (a c : Fin 6) : ⁅(F a).range, (F c).range⁆ ≤ K a c := by
    fin_cases a <;> fin_cases c
    · exact rootRange_self_commutator_le _ _
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h05
    · exact hreverse 0 1 h01
    · exact rootRange_self_commutator_le _ _
    · exact h12
    · exact h13
    · exact h14
    · exact h15
    · exact hreverse 0 2 h02
    · exact hreverse 1 2 h12
    · exact rootRange_self_commutator_le _ _
    · exact h23
    · exact h24
    · exact h25
    · exact hreverse 0 3 h03
    · exact hreverse 1 3 h13
    · exact hreverse 2 3 h23
    · exact rootRange_self_commutator_le _ _
    · exact h34
    · exact h35
    · exact hreverse 0 4 h04
    · exact hreverse 1 4 h14
    · exact hreverse 2 4 h24
    · exact hreverse 3 4 h34
    · exact rootRange_self_commutator_le _ _
    · exact h45
    · exact hreverse 0 5 h05
    · exact hreverse 1 5 h15
    · exact hreverse 2 5 h25
    · exact hreverse 3 5 h35
    · exact hreverse 4 5 h45
    · exact rootRange_self_commutator_le _ _
  have hindex (γ : {γ : ι // b.IsPos γ})
      (hγ : γ.val = i.val ∨ γ.val = j.val ∨ γ.val = P.reflectionPerm j.val i.val ∨
        γ.val = P.reflectionPerm i.val (P.reflectionPerm j.val i.val) ∨
        γ.val = P.reflectionPerm i.val j.val ∨
        γ.val = P.reflectionPerm j.val (P.reflectionPerm i.val j.val)) :
      ∃ a : Fin 6, label a = γ.val := by
    rcases hγ with hi | hj | hz | hw | hv | hh
    · exact ⟨0, hi.symm⟩
    · exact ⟨1, hj.symm⟩
    · exact ⟨2, hz.symm⟩
    · exact ⟨3, hw.symm⟩
    · exact ⟨4, hv.symm⟩
    · exact ⟨5, hh.symm⟩
  obtain ⟨a, ha⟩ := hindex α hα
  obtain ⟨c, hc'⟩ := hindex β hβ
  rw [← hrange a α ha, ← hrange c β hc']
  simpa only [K, ha, hc'] using hlocal a c

end Atlas.Chevalley
