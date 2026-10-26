import Atlas.LinearGroups.Chevalley.PositiveRootCanonicalFamily
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-! Actual normalizer transport of the literal positive-root subgroups.
Transporting a retained witness is independent of coherence; identifying its
range with the chosen target subgroup uses the proved positive coherence.
No pointwise normalization, pair reduction, or collection is asserted. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule Atlas.GroupTheory

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

/-- Left multiplication by an actual normalizer element transports the
retained root label by its actual root permutation. -/
def weightCompanionRootLift_normalizerMul {β : ι}
    (L : WeightCompanionRootLift P b O hc hm R β)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R) :
    WeightCompanionRootLift P b O hc hm R
      (weightCompanionNRootPermHom P b O hc hm R n β) where
  simple := L.simple
  lift := n * L.lift
  root_eq := by
    rw [map_mul]
    change weightCompanionNRootPermHom P b O hc hm R n
        (weightCompanionNRootPermHom P b O hc hm R L.lift L.simple.val) = _
    rw [L.root_eq]

theorem weightCompanionRootLiftHom_normalizerMul {β : ι}
    (L : WeightCompanionRootLift P b O hc hm R β)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (s : Multiplicative R) :
    weightCompanionRootLiftHom P b O hc hm R
        (weightCompanionRootLift_normalizerMul P b O hc hm R L n) s =
      n.val * weightCompanionRootLiftHom P b O hc hm R L s * n.val⁻¹ := by
  change (n.val * L.lift.val) * weightCompanionX P b O hc hm R L.simple s.toAdd *
      (n.val * L.lift.val)⁻¹ =
    n.val * (L.lift.val * weightCompanionX P b O hc hm R L.simple s.toAdd *
      L.lift.val⁻¹) * n.val⁻¹
  group

/-- This equality retains both the parameter homomorphism and its new witness;
it needs no positivity, simple-diamond premise, or coherence theorem. -/
theorem weightCompanionRootLiftSubgroup_normalizerMul {β : ι}
    (L : WeightCompanionRootLift P b O hc hm R β)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R) :
    weightCompanionRootLiftSubgroup P b O hc hm R
        (weightCompanionRootLift_normalizerMul P b O hc hm R L n) =
      conjugateSubgroup n.val (weightCompanionRootLiftSubgroup P b O hc hm R L) := by
  rw [weightCompanionRootLiftSubgroup, weightCompanionRootLiftSubgroup,
    conjugateSubgroup_range]
  congr 1
  apply MonoidHom.ext
  intro s
  exact weightCompanionRootLiftHom_normalizerMul P b O hc hm R L n s

/-- If the initial and final labels are positive, actual normalizer conjugation
transports their literal chosen root subgroups. Parameters may be rescaled. -/
theorem positiveWeightCompanionRootSubgroup_conjugate
    (hdiamond : SimpleDiamondProducts P b)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (β : {β : ι // b.IsPos β})
    (hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n β.val)) :
    conjugateSubgroup n.val (positiveWeightCompanionRootSubgroup P b O hc hm R β) =
      positiveWeightCompanionRootSubgroup P b O hc hm R
        ⟨weightCompanionNRootPermHom P b O hc hm R n β.val, hpos⟩ := by
  change conjugateSubgroup n.val
    (weightCompanionRootLiftSubgroup P b O hc hm R
      (positiveRootChosenLift P b O hc hm R β)) = _
  exact (weightCompanionRootLiftSubgroup_normalizerMul P b O hc hm R
    (positiveRootChosenLift P b O hc hm R β) n).symm.trans
      (rootLiftSubgroup_eq_positiveWeightCompanionRootSubgroup P b O hc hm R
        hdiamond ⟨weightCompanionNRootPermHom P b O hc hm R n β.val, hpos⟩
        (weightCompanionRootLift_normalizerMul P b O hc hm R
          (positiveRootChosenLift P b O hc hm R β) n))

/-- Actual commutator subgroups transport together with their two positive
root labels. This supplies transport, not the still-required local containment. -/
theorem positiveWeightCompanionRootSubgroup_commutator_conjugate
    (hdiamond : SimpleDiamondProducts P b)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (α β : {β : ι // b.IsPos β})
    (hα : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n α.val))
    (hβ : b.IsPos (weightCompanionNRootPermHom P b O hc hm R n β.val)) :
    conjugateSubgroup n.val
        ⁅positiveWeightCompanionRootSubgroup P b O hc hm R α,
          positiveWeightCompanionRootSubgroup P b O hc hm R β⁆ =
      ⁅positiveWeightCompanionRootSubgroup P b O hc hm R
          ⟨weightCompanionNRootPermHom P b O hc hm R n α.val, hα⟩,
        positiveWeightCompanionRootSubgroup P b O hc hm R
          ⟨weightCompanionNRootPermHom P b O hc hm R n β.val, hβ⟩⁆ := by
  change Subgroup.map (MulAut.conj n.val).toMonoidHom _ = _
  rw [Subgroup.map_commutator]
  change ⁅conjugateSubgroup n.val (positiveWeightCompanionRootSubgroup P b O hc hm R α),
    conjugateSubgroup n.val (positiveWeightCompanionRootSubgroup P b O hc hm R β)⁆ = _
  rw [positiveWeightCompanionRootSubgroup_conjugate P b O hc hm R hdiamond n α hα,
    positiveWeightCompanionRootSubgroup_conjugate P b O hc hm R hdiamond n β hβ]

end Atlas.Chevalley
