import Atlas.LinearGroups.Chevalley.OppositePositiveWitnessedIntersection

/-! Every retained negative-root family belongs to the actual longest-lift
conjugate of U. This is witnessed group membership, not an inference from
lower triangularity of its adjoint image. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

theorem rootLiftHom_mem_oppositePositiveWitnessed {β : ι}
    (hβ : ¬ b.IsPos β) (L : WeightCompanionRootLift P b O hc hm R β)
    (t : Multiplicative R) :
    weightCompanionRootLiftHom P b O hc hm R L t ∈
      oppositePositiveWitnessedWeightCompanionSubgroup P b O hc hm R := by
  let n := weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)
  have hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n⁻¹ β) := by
    rw [map_inv]
    change b.IsPos ((weightCompanionNRootPermHom P b O hc hm R
      (weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)))⁻¹ β)
    rw [weightCompanionNRootPermHom_titsLift]
    change b.IsPos (((rootWeylLongest P b)⁻¹).val β)
    rw [rootWeylLongest_inv]
    exact (rootWeylLongest_isPos_iff P b β).mpr hβ
  let L' := weightCompanionRootLift_normalizerMul P b O hc hm R L n⁻¹
  have hu := rootLiftHom_mem_positiveWitnessedWeightCompanionSubgroup
    P b O hc hm R hpos L' t
  refine ⟨weightCompanionRootLiftHom P b O hc hm R L' t, hu, ?_⟩
  change n.val * weightCompanionRootLiftHom P b O hc hm R L' t * n.val⁻¹ = _
  dsimp only [L']
  rw [weightCompanionRootLiftHom_normalizerMul]
  change n.val * (n.val⁻¹ * weightCompanionRootLiftHom P b O hc hm R L t *
    (n.val⁻¹)⁻¹) * n.val⁻¹ = _
  group

end Atlas.Chevalley
