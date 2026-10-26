import Atlas.GroupTheory.RootFamilyCommutators
import Atlas.LinearGroups.Chevalley.PositiveRootConeSubgroup
import Atlas.LinearGroups.Chevalley.LiteralPositiveRootRanges
import Atlas.LinearGroups.Chevalley.WeightCompanionSmallRankPositivePairs
import Atlas.LinearGroups.Chevalley.WeightCompanionNonAdjacentWeyl
import Atlas.LinearGroups.Chevalley.RootData.SmallRankCommutatorRootCones
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Complete local subgroup containment for the two-, three-, and four-root
positive systems. Cases are root labels, never elements of a finite group. -/
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

/-- All pairs in the two-root A1×A1 positive system, including equal labels. -/
theorem positiveRootSubgroup_a1xa1_local_cone
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = 0) (hji : b.cartanMatrix j i = 0)
    (α β : {γ : ι // b.IsPos γ})
    (hα : α.val = i.val ∨ α.val = j.val)
    (hβ : β.val = i.val ∨ β.val = j.val) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
  have hrange (k : b.support) (γ : {γ : ι // b.IsPos γ}) (hk : γ.val = k.val) :
      positiveWeightCompanionRootSubgroup P b O hc hm R γ =
        (weightCompanionXHom P b O hc hm R k).range := by
    have he : γ = ⟨k.val, b.isPos_of_mem_support k.property⟩ := Subtype.ext hk
    rw [he, weightCompanionXHom_range_eq_positiveRoot P b O hc hm R hdiamond k]
  rcases hα with ha | ha <;> rcases hβ with hb | hb
  · rw [hrange i α ha, hrange i β hb]
    exact rootRange_self_commutator_le _ _
  · rw [hrange i α ha, hrange j β hb]
    apply rootRange_commutator_le_of_commute
    intro s t
    exact weightCompanionX_commute_of_zero_cartan P b hdiamond O hc hm R i j hne hji s t
  · rw [hrange j α ha, hrange i β hb]
    apply rootRange_commutator_le_of_commute
    intro s t
    exact weightCompanionX_commute_of_zero_cartan P b hdiamond O hc hm R j i hne.symm hij s t
  · rw [hrange j α ha, hrange j β hb]
    exact rootRange_self_commutator_le _ _

/-- For every pair among the three literal A2 positive labels, the actual
chosen root-subgroup commutator lies in the cone on that pair. -/
theorem positiveRootSubgroup_a2_local_cone
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1)
    (α β : {γ : ι // b.IsPos γ})
    (hα : α.val = i.val ∨ α.val = j.val ∨ α.val = P.reflectionPerm i.val j.val)
    (hβ : β.val = i.val ∨ β.val = j.val ∨ β.val = P.reflectionPerm i.val j.val) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
  let ni := weightCompanionWeyl P b O hc hm R i 1
  let X := weightCompanionXHom P b O hc hm R i
  let Y := weightCompanionXHom P b O hc hm R j
  let Z := (MulAut.conj ni).toMonoidHom.comp Y
  let F : Fin 3 → (Multiplicative R →* WeightCompanion P b O hc hm R) := ![X, Y, Z]
  let label : Fin 3 → ι := ![i.val, j.val, P.reflectionPerm i.val j.val]
  let K := fun a c : Fin 3 => positiveWeightCompanionConeSubgroup P b O hc hm R (label a) (label c)
  have hrange (a : Fin 3) (γ : {γ : ι // b.IsPos γ}) (ha : label a = γ.val) :
      (F a).range = positiveWeightCompanionRootSubgroup P b O hc hm R γ := by
    fin_cases a
    · exact (weightCompanionXHom_range_eq_positiveRoot P b O hc hm R hdiamond i).trans
        (congrArg (positiveWeightCompanionRootSubgroup P b O hc hm R) (Subtype.ext ha))
    · exact (weightCompanionXHom_range_eq_positiveRoot P b O hc hm R hdiamond j).trans
        (congrArg (positiveWeightCompanionRootSubgroup P b O hc hm R) (Subtype.ext ha))
    · apply weightCompanion_conjugateXHom_range_eq_positiveRoot
        P b O hc hm R hdiamond (weightCompanionSimpleWeylInN P b O hc hm R i) j γ.val γ.property
      rw [weightCompanionNRootPermHom_simple]
      exact ha
  have hzcone := a2_literal_commutator_root_cone P b i.val j.val hji
  have hzpos := positiveIntegralRootCone_isPos P b hzcone
    (b.isPos_of_mem_support i.property) (b.isPos_of_mem_support j.property)
  have hzmem (t : R) : Z (Multiplicative.ofAdd t) ∈ K 0 1 := by
    apply positiveWeightCompanionRootSubgroup_le_cone P b O hc hm R i.val j.val
      ⟨P.reflectionPerm i.val j.val, hzpos⟩ hzcone
    rw [← hrange 2 ⟨P.reflectionPerm i.val j.val, hzpos⟩ rfl]
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  have h01 : ⁅(F 0).range, (F 1).range⁆ ≤ K 0 1 := by
    apply rootRange_commutator_le
    intro s t
    change ⁅weightCompanionX P b O hc hm R i s, weightCompanionX P b O hc hm R j t⁆ ∈ _
    rw [(weightCompanion_a2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).1]
    exact hzmem (s * t)
  have h02 : ⁅(F 0).range, (F 2).range⁆ ≤ K 0 2 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    exact (weightCompanion_a2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).2.1
  have h12 : ⁅(F 1).range, (F 2).range⁆ ≤ K 1 2 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    exact (weightCompanion_a2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).2.2
  have hreverse (a c : Fin 3) (h : ⁅(F a).range, (F c).range⁆ ≤ K a c) :
      ⁅(F c).range, (F a).range⁆ ≤ K c a := by
    change _ ≤ positiveWeightCompanionConeSubgroup P b O hc hm R (label c) (label a)
    rw [Subgroup.commutator_comm,
      positiveWeightCompanionConeSubgroup_comm P b O hc hm R (label c) (label a)]
    exact h
  have hlocal (a c : Fin 3) : ⁅(F a).range, (F c).range⁆ ≤ K a c := by
    fin_cases a <;> fin_cases c
    · exact rootRange_self_commutator_le _ _
    · exact h01
    · exact h02
    · exact hreverse 0 1 h01
    · exact rootRange_self_commutator_le _ _
    · exact h12
    · exact hreverse 0 2 h02
    · exact hreverse 1 2 h12
    · exact rootRange_self_commutator_le _ _
  have hindex (γ : {γ : ι // b.IsPos γ})
      (hγ : γ.val = i.val ∨ γ.val = j.val ∨ γ.val = P.reflectionPerm i.val j.val) :
      ∃ a : Fin 3, label a = γ.val := by
    rcases hγ with hi | hj | hz
    · exact ⟨0, hi.symm⟩
    · exact ⟨1, hj.symm⟩
    · exact ⟨2, hz.symm⟩
  obtain ⟨a, ha⟩ := hindex α hα
  obtain ⟨c, hc'⟩ := hindex β hβ
  rw [← hrange a α ha, ← hrange c β hc']
  simpa only [K, ha, hc'] using hlocal a c

set_option maxHeartbeats 2000000 in
/-- Every pair among the four B2 positive labels, including the two distinct
short roots, satisfies the cone containment in the actual chosen model. -/
theorem positiveRootSubgroup_b2_local_cone
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2)
    (α β : {γ : ι // b.IsPos γ})
    (hα : α.val = i.val ∨ α.val = j.val ∨ α.val = P.reflectionPerm j.val i.val ∨
      α.val = P.reflectionPerm i.val j.val)
    (hβ : β.val = i.val ∨ β.val = j.val ∨ β.val = P.reflectionPerm j.val i.val ∨
      β.val = P.reflectionPerm i.val j.val) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
  let ni := weightCompanionWeyl P b O hc hm R i 1
  let nj := weightCompanionWeyl P b O hc hm R j 1
  let X := weightCompanionXHom P b O hc hm R i
  let Y := weightCompanionXHom P b O hc hm R j
  let Z := (MulAut.conj nj).toMonoidHom.comp X
  let V := (MulAut.conj ni).toMonoidHom.comp Y
  have hxval (a : R) : X (Multiplicative.ofAdd a) =
      weightCompanionX P b O hc hm R i a := rfl
  have hyval (a : R) : Y (Multiplicative.ofAdd a) =
      weightCompanionX P b O hc hm R j a := rfl
  have hzval (a : R) : Z (Multiplicative.ofAdd a) =
      nj * weightCompanionX P b O hc hm R i a * nj⁻¹ := by
    simp only [Z, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hxval]
  have hvval (a : R) : V (Multiplicative.ofAdd a) =
      ni * weightCompanionX P b O hc hm R j a * ni⁻¹ := by
    simp only [V, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hyval]
  have hxy (s t : R) :
      ⁅X (Multiplicative.ofAdd s), Y (Multiplicative.ofAdd t)⁆ =
        Z (Multiplicative.ofAdd (-s * t)) * V (Multiplicative.ofAdd (s ^ 2 * t)) := by
    rw [hxval, hyval, hzval, hvval]
    simpa only [ni, nj] using
      (weightCompanion_b2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).1
  have hxz (s t : R) :
      ⁅X (Multiplicative.ofAdd s), Z (Multiplicative.ofAdd t)⁆ =
        V (Multiplicative.ofAdd (-2 * s * t)) := by
    rw [hxval, hzval, hvval]
    simpa only [ni, nj] using
      (weightCompanion_b2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).2.1
  let F : Fin 4 → (Multiplicative R →* WeightCompanion P b O hc hm R) := ![X, Y, Z, V]
  let label : Fin 4 → ι := ![i.val, j.val, P.reflectionPerm j.val i.val,
    P.reflectionPerm i.val j.val]
  let K := fun a c : Fin 4 => positiveWeightCompanionConeSubgroup P b O hc hm R (label a) (label c)
  have hrange (a : Fin 4) (γ : {γ : ι // b.IsPos γ}) (ha : label a = γ.val) :
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
        P b O hc hm R hdiamond (weightCompanionSimpleWeylInN P b O hc hm R i) j γ.val γ.property
      rw [weightCompanionNRootPermHom_simple]
      exact ha
  obtain ⟨hzcone, hvcone, hazcone⟩ := b2_literal_commutator_root_cones P b i.val j.val hij hji
  have hzpos := positiveIntegralRootCone_isPos P b hzcone
    (b.isPos_of_mem_support i.property) (b.isPos_of_mem_support j.property)
  have hvpos := positiveIntegralRootCone_isPos P b hvcone
    (b.isPos_of_mem_support i.property) (b.isPos_of_mem_support j.property)
  have hzmem (a c : Fin 4)
      (hz : PositiveIntegralRootCone P b (label a) (label c) (P.reflectionPerm j.val i.val))
      (t : R) : Z (Multiplicative.ofAdd t) ∈ K a c := by
    apply positiveWeightCompanionRootSubgroup_le_cone P b O hc hm R (label a) (label c)
      ⟨P.reflectionPerm j.val i.val, hzpos⟩ hz
    rw [← hrange 2 ⟨P.reflectionPerm j.val i.val, hzpos⟩ rfl]
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  have hvmem (a c : Fin 4)
      (hv : PositiveIntegralRootCone P b (label a) (label c) (P.reflectionPerm i.val j.val))
      (t : R) : V (Multiplicative.ofAdd t) ∈ K a c := by
    apply positiveWeightCompanionRootSubgroup_le_cone P b O hc hm R (label a) (label c)
      ⟨P.reflectionPerm i.val j.val, hvpos⟩ hv
    rw [← hrange 3 ⟨P.reflectionPerm i.val j.val, hvpos⟩ rfl]
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  have h01 : ⁅(F 0).range, (F 1).range⁆ ≤ K 0 1 := by
    apply rootRange_commutator_le X Y (K 0 1)
    intro s t
    rw [hxy]
    exact (K 0 1).mul_mem
      (x := Z (Multiplicative.ofAdd (-s * t)))
      (y := V (Multiplicative.ofAdd (s ^ 2 * t)))
      (hzmem 0 1 hzcone (-s * t)) (hvmem 0 1 hvcone (s ^ 2 * t))
  have h02 : ⁅(F 0).range, (F 2).range⁆ ≤ K 0 2 := by
    apply rootRange_commutator_le X Z (K 0 2)
    intro s t
    rw [hxz]
    exact hvmem 0 2 hazcone (-2 * s * t)
  have h03 : ⁅(F 0).range, (F 3).range⁆ ≤ K 0 3 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    exact (weightCompanion_b2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).2.2.1
  have h12 : ⁅(F 1).range, (F 2).range⁆ ≤ K 1 2 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    exact (weightCompanion_b2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).2.2.2.1
  have h13 : ⁅(F 1).range, (F 3).range⁆ ≤ K 1 3 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    exact (weightCompanion_b2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).2.2.2.2.1
  have h23 : ⁅(F 2).range, (F 3).range⁆ ≤ K 2 3 := by
    apply rootRange_commutator_le_of_commute
    intro s t
    exact (weightCompanion_b2_positive_pairs P b hdiamond O hc hm R i j hne hij hji s t).2.2.2.2.2
  have hreverse (a c : Fin 4) (h : ⁅(F a).range, (F c).range⁆ ≤ K a c) :
      ⁅(F c).range, (F a).range⁆ ≤ K c a := by
    change _ ≤ positiveWeightCompanionConeSubgroup P b O hc hm R (label c) (label a)
    rw [Subgroup.commutator_comm,
      positiveWeightCompanionConeSubgroup_comm P b O hc hm R (label c) (label a)]
    exact h
  have hlocal (a c : Fin 4) : ⁅(F a).range, (F c).range⁆ ≤ K a c := by
    fin_cases a <;> fin_cases c
    · exact rootRange_self_commutator_le _ _
    · exact h01
    · exact h02
    · exact h03
    · exact hreverse 0 1 h01
    · exact rootRange_self_commutator_le _ _
    · exact h12
    · exact h13
    · exact hreverse 0 2 h02
    · exact hreverse 1 2 h12
    · exact rootRange_self_commutator_le _ _
    · exact h23
    · exact hreverse 0 3 h03
    · exact hreverse 1 3 h13
    · exact hreverse 2 3 h23
    · exact rootRange_self_commutator_le _ _
  have hindex (γ : {γ : ι // b.IsPos γ})
      (hγ : γ.val = i.val ∨ γ.val = j.val ∨ γ.val = P.reflectionPerm j.val i.val ∨
        γ.val = P.reflectionPerm i.val j.val) : ∃ a : Fin 4, label a = γ.val := by
    rcases hγ with hi | hj | hz | hv
    · exact ⟨0, hi.symm⟩
    · exact ⟨1, hj.symm⟩
    · exact ⟨2, hz.symm⟩
    · exact ⟨3, hv.symm⟩
  obtain ⟨a, ha⟩ := hindex α hα
  obtain ⟨c, hc'⟩ := hindex β hβ
  rw [← hrange a α ha, ← hrange c β hc']
  simpa only [K, ha, hc'] using hlocal a c

end Atlas.Chevalley
