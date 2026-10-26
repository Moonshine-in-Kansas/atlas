import Atlas.LinearGroups.Chevalley.PositiveRootConeSubgroup
import Atlas.LinearGroups.Chevalley.PositiveRootNormalizerTransport
import Atlas.LinearGroups.Chevalley.WeightCompanionFullWeylImage
import Atlas.LinearGroups.Chevalley.RootData.PositivePairSimpleSupport

/-! Transport of strict root cones and reduction of arbitrary positive-root
commutators to complete local tables on two-simple support. The local table
premise remains explicit and is not inferred merely from root-label geometry. -/
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

/-- Conjugation transports the whole cone subgroup into the cone on the
transported inputs. Their positivity implies positivity of every output. -/
theorem positiveWeightCompanionConeSubgroup_conjugate_le
    (hdiamond : SimpleDiamondProducts P b)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (α β : {γ : ι // b.IsPos γ})
    (hα : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n α.val))
    (hβ : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n β.val)) :
    conjugateSubgroup n.val (positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val) ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R
        (weightCompanionNRootPermHom P b O hc hm R n α.val)
        (weightCompanionNRootPermHom P b O hc hm R n β.val) := by
  have hn : weightCompanionNRootPermHom P b O hc hm R n ∈ P.weylGroupToPerm.range := by
    rw [← weightCompanionNRootPermHom_range_eq_weylImage P b O hc hm R]
    exact ⟨n, rfl⟩
  let w : P.weylGroupToPerm.range := ⟨weightCompanionNRootPermHom P b O hc hm R n, hn⟩
  change (⨆ γ : {γ : {γ : ι // b.IsPos γ} // PositiveIntegralRootCone P b α.val β.val γ.val},
      positiveWeightCompanionRootSubgroup P b O hc hm R γ.val).map
        (MulAut.conj n.val).toMonoidHom ≤ _
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro γ
  have hcone := positiveIntegralRootCone_weyl P b w γ.property
  have hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n γ.val.val) :=
    positiveIntegralRootCone_isPos P b hcone hα hβ
  change conjugateSubgroup n.val
    (positiveWeightCompanionRootSubgroup P b O hc hm R γ.val) ≤ _
  rw [positiveWeightCompanionRootSubgroup_conjugate P b O hc hm R hdiamond n γ.val hpos]
  exact positiveWeightCompanionRootSubgroup_le_cone P b O hc hm R _ _
    ⟨weightCompanionNRootPermHom P b O hc hm R n γ.val.val, hpos⟩ hcone

/-- Actual positive-root subgroup commutator containment transports with the
actual normalizer element. This does not identify pointwise root parameters. -/
theorem positiveRootSubgroup_commutator_cone_of_normalizer_transport
    (hdiamond : SimpleDiamondProducts P b)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (α β : {γ : ι // b.IsPos γ})
    (hα : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n α.val))
    (hβ : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n β.val))
    (hlocal : ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R
        ⟨weightCompanionNRootPermHom P b O hc hm R n α.val, hα⟩,
      positiveWeightCompanionRootSubgroup P b O hc hm R
        ⟨weightCompanionNRootPermHom P b O hc hm R n β.val, hβ⟩⁆ ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R
        (weightCompanionNRootPermHom P b O hc hm R n α.val)
        (weightCompanionNRootPermHom P b O hc hm R n β.val) := by
  rw [← positiveWeightCompanionRootSubgroup_commutator_conjugate
    P b O hc hm R hdiamond n α β hα hβ]
  exact (Subgroup.map_mono (f := (MulAut.conj n.val).toMonoidHom) hlocal).trans
    (positiveWeightCompanionConeSubgroup_conjugate_le P b O hc hm R hdiamond n α β hα hβ)

variable (hdiamond : SimpleDiamondProducts P b)
  (hlocal : ∀ i j : b.support, i ≠ j →
    ∀ α β : {γ : ι // b.IsPos γ}, α ≠ β →
      (rootSimpleCoefficients P b α.val).support ⊆ {i, j} →
      (rootSimpleCoefficients P b β.val).support ⊆ {i, j} →
      ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
        positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
        positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val)

include hdiamond hlocal

/-- Complete local two-simple-support tables suffice for every distinct
positive-root pair. The reduced pair may be any two positive local roots. -/
theorem positiveRootSubgroup_commutator_cone_of_rankTwo_tables
    (α β : {γ : ι // b.IsPos γ}) (hne : α ≠ β) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      positiveWeightCompanionConeSubgroup P b O hc hm R α.val β.val := by
  obtain ⟨w, i, j, hij, a, c, hac, hwa, hwc, has, hcs⟩ :=
    exists_positive_pair_simple_support P b α β hne
  have hw : w.val ∈ (weightCompanionNRootPermHom P b O hc hm R).range := by
    rw [weightCompanionNRootPermHom_range_eq_weylImage P b O hc hm R]
    exact w.property
  obtain ⟨n, hn⟩ := hw
  have hna : weightCompanionNRootPermHom P b O hc hm R n a.val = α.val := by
    rw [hn]
    exact hwa
  have hnc : weightCompanionNRootPermHom P b O hc hm R n c.val = β.val := by
    rw [hn]
    exact hwc
  have hpa : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n a.val) := by
    rw [hna]
    exact α.property
  have hpc : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n c.val) := by
    rw [hnc]
    exact β.property
  have h := positiveRootSubgroup_commutator_cone_of_normalizer_transport
    P b O hc hm R hdiamond n a c hpa hpc (hlocal i j hij a c hac has hcs)
  simpa only [hna, hnc] using h

/-- The precise actual subgroup-height premise of conditional collection
follows from complete local tables, using original-height cone transport. -/
theorem positiveRootSubgroup_height_commutators_of_rankTwo_tables
    (α β : {γ : ι // b.IsPos γ}) (hne : α ≠ β) :
    ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
      positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ ≤
      ⨆ γ : {γ : {γ : ι // b.IsPos γ} // b.height β.val < b.height γ.val},
        positiveWeightCompanionRootSubgroup P b O hc hm R γ.val :=
  (positiveRootSubgroup_commutator_cone_of_rankTwo_tables
    P b O hc hm R hdiamond hlocal α β hne).trans
      (positiveWeightCompanionConeSubgroup_le_height_tail P b O hc hm R α β)

end Atlas.Chevalley
