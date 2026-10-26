import Atlas.GroupTheory.RootScalingConjugateFamilies
import Atlas.LinearGroups.Chevalley.WeightCompanionWeylQuotientIdentification
import Atlas.LinearGroups.Chevalley.PositiveRootWeylLifts

/-! A first coherence result for actual witnessed root families: two N lifts
with the same full root permutation give the same conjugate of a fixed simple
root subgroup. This does not identify arbitrary lifts merely having the same
image of one simple root. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

/-- Equal full root permutations imply unit-rescaled equality of the actual
conjugate simple-root families. The kernel theorem is used as a proved input,
not as an extra faithfulness assumption. -/
theorem weightCompanion_rootConjugates_of_sameRootPermutation
    (hdiamond : SimpleDiamondProducts P b) (i : b.support)
    (n m : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (hperm : weightCompanionNRootPermHom P b O hc hm R n =
      weightCompanionNRootPermHom P b O hc hm R m) :
    ∃ a : Rˣ, ∀ t : R,
      m.val * weightCompanionX P b O hc hm R i t * m.val⁻¹ =
        n.val * weightCompanionX P b O hc hm R i (a.val * t) * n.val⁻¹ := by
  have ht : (n⁻¹ * m).val ∈ weightCompanionTorusSubgroup P b O hc hm R := by
    change n⁻¹ * m ∈
      (weightCompanionTorusSubgroup P b O hc hm R).subgroupOf
        (weightCompanionExtendedWeylSubgroup P b O hc hm R)
    rw [← weightCompanionNRootPermHom_ker_eq_torus P b O hc hm R hdiamond]
    change weightCompanionNRootPermHom P b O hc hm R (n⁻¹ * m) = 1
    rw [map_mul, map_inv, hperm, inv_mul_cancel]
  exact Atlas.GroupTheory.rootScaling_conjugates_of_inv_mul
    (weightCompanionX P b O hc hm R i) n.val m.val
    (weightCompanionTorusSubgroup_le_X_scaling P b O hc hm R i ht)

/-- Same simple origin and same full Weyl permutation imply equality of the
already constructed witnessed root subgroups. The parameter maps themselves
may differ by the unit rescaling exhibited above. -/
theorem weightCompanionRootLiftSubgroup_eq_of_same_rootPermutation
    (hdiamond : SimpleDiamondProducts P b) {β : ι}
    (L L' : WeightCompanionRootLift P b O hc hm R β)
    (hsimple : L.simple = L'.simple)
    (hperm : weightCompanionNRootPermHom P b O hc hm R L.lift =
      weightCompanionNRootPermHom P b O hc hm R L'.lift) :
    weightCompanionRootLiftSubgroup P b O hc hm R L =
      weightCompanionRootLiftSubgroup P b O hc hm R L' := by
  obtain ⟨a, ha⟩ := weightCompanion_rootConjugates_of_sameRootPermutation
    P b O hc hm R hdiamond L.simple L.lift L'.lift hperm
  have hfamily (t : R) :
      weightCompanionRootLiftHom P b O hc hm R L' (Multiplicative.ofAdd t) =
        weightCompanionRootLiftHom P b O hc hm R L
          (Multiplicative.ofAdd (a.val * t)) := by
    simpa only [weightCompanionRootLiftHom_apply, toAdd_ofAdd,
      ← hsimple] using ha t
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Multiplicative.ofAdd ((a⁻¹).val * t.toAdd), ?_⟩
    rw [hfamily]
    have hcancel : a.val * ((a⁻¹).val * t.toAdd) = t.toAdd := by
      simp [← mul_assoc]
    rw [hcancel, ofAdd_toAdd]
  · rintro ⟨t, rfl⟩
    refine ⟨Multiplicative.ofAdd (a.val * t.toAdd), ?_⟩
    simpa only [ofAdd_toAdd] using (hfamily t.toAdd).symm

end Atlas.Chevalley
