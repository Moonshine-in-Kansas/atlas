import Atlas.LinearGroups.Chevalley.OppositePositiveWitnessedIntersection
import Atlas.LinearGroups.Chevalley.WeightCompanionExtendedWeyl

/-! The actual upper and longest-conjugate upper subgroups intersect in T.
This follows from U-minus intersect B=1 and torus normalization, without counts. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
open scoped Pointwise
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

theorem mem_torus_of_mem_positiveWitnessed_and_opposite_join
    (hdiamond : SimpleDiamondProducts P b)
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveWitnessedTorusJoin P b O hc hm R)
    (hop : g ∈ conjugateSubgroup
      (weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)).val
      (positiveWitnessedTorusJoin P b O hc hm R)) :
    g ∈ weightCompanionTorusSubgroup P b O hc hm R := by
  let n := weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)
  let U := positiveWitnessedWeightCompanionSubgroup P b O hc hm R
  let T := weightCompanionTorusSubgroup P b O hc hm R
  let B := positiveWitnessedTorusJoin P b O hc hm R
  obtain ⟨a, ha, he⟩ := hop
  change n.val * a * n.val⁻¹ = g at he
  have hprod : a ∈ (U : Set (WeightCompanion P b O hc hm R)) *
      (T : Set (WeightCompanion P b O hc hm R)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U T
      (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)]
    exact ha
  obtain ⟨u, hu, t, ht, hut⟩ := hprod
  have hnt : n.val * t * n.val⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp
      (weightCompanionExtendedWeylSubgroup_le_torusNormalizer P b O hc hm R n.property) t).mp ht
  have huo : n.val * u * n.val⁻¹ ∈
      oppositePositiveWitnessedWeightCompanionSubgroup P b O hc hm R :=
    ⟨u, hu, rfl⟩
  have hfactor : n.val * u * n.val⁻¹ = g * (n.val * t * n.val⁻¹)⁻¹ := by
    rw [← he, ← hut]
    group
  have hub : n.val * u * n.val⁻¹ ∈ B := by
    rw [hfactor]
    exact B.mul_mem hg (B.inv_mem ((show T ≤ B from le_sup_right) hnt))
  have hu1 := oppositePositiveWitnessed_eq_one_of_mem_torusJoin
    P b O hc hm R hdiamond _ huo hub
  have heq : g = n.val * t * n.val⁻¹ := by
    calc
      g = (n.val * u * n.val⁻¹) * (n.val * t * n.val⁻¹) := by
        rw [← he, ← hut]
        group
      _ = n.val * t * n.val⁻¹ := by rw [hu1, one_mul]
  rw [heq]
  exact hnt

theorem positiveWitnessedTorusJoin_inf_longest_conjugate_eq_torus
    (hdiamond : SimpleDiamondProducts P b) :
    positiveWitnessedTorusJoin P b O hc hm R ⊓
      conjugateSubgroup
        (weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)).val
        (positiveWitnessedTorusJoin P b O hc hm R) =
      weightCompanionTorusSubgroup P b O hc hm R := by
  apply le_antisymm
  · rintro g ⟨hg, hop⟩
    exact mem_torus_of_mem_positiveWitnessed_and_opposite_join
      P b O hc hm R hdiamond g hg hop
  · intro g hg
    have hTB : weightCompanionTorusSubgroup P b O hc hm R ≤
        positiveWitnessedTorusJoin P b O hc hm R := le_sup_right
    refine ⟨hTB hg, ?_⟩
    let n := weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)
    have hnt : n.val⁻¹ * g * n.val ∈ weightCompanionTorusSubgroup P b O hc hm R := by
      have hn := weightCompanionExtendedWeylSubgroup_le_torusNormalizer
        P b O hc hm R (show n.val⁻¹ ∈ weightCompanionExtendedWeylSubgroup P b O hc hm R from
          (weightCompanionExtendedWeylSubgroup P b O hc hm R).inv_mem n.property)
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hn g).mp hg
    refine ⟨n.val⁻¹ * g * n.val, hTB hnt, ?_⟩
    change n.val * (n.val⁻¹ * g * n.val) * n.val⁻¹ = g
    group

end Atlas.Chevalley
