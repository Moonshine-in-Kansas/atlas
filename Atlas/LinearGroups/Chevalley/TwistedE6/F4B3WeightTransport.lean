import Atlas.LinearGroups.Chevalley.TwistedE6.ClassicalBWeights
import Atlas.LinearGroups.Chevalley.TwistedE6.F4RootWeights
import Atlas.LinearGroups.Chevalley.RootData.F4B3Parabolic

/-! The existing actual B3-to-F4 parabolic identification preserves the
long-two/short-one inversion statistic, with the original simple markings. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.F4B3WeightTransport
open Classical ClassicalData RootData WeightedRootInversions WeightedWeylTransport

theorem rootWeight_markedSimple (i : (baseB 2).support) :
    F4RootWeights.rootWeight (F4B3.markedSimple i).val =
      ClassicalBWeights.rootWeight 2 i.val := by
  obtain ⟨k, rfl⟩ := (baseBIndexEquiv 2).surjective i
  simp only [F4B3.markedSimple, Equiv.symm_apply_apply, F4RootWeights.rootWeight_simple]
  change e6FoldedWeylWeight k.castSucc =
    ClassicalBWeights.rootWeight 2 (ClassicalBParabolic.simple 2 k).val
  rw [ClassicalBWeights.rootWeight_simple]
  fin_cases k <;> norm_num [e6FoldedWeylWeight]

theorem weylHom_weightedInversions (w : ClassicalBParabolic.W 2) :
    F4RootWeights.f4WeightedInversions (F4B3.weylHom w) =
      ClassicalBWeights.bWeightedInversions 2 w := by
  exact weightedInversions_transport
    (pairingB 3) (baseB 2) (ClassicalBWeights.rootWeight 2)
    F4Data.pairing F4Data.base F4RootWeights.rootWeight
    (ClassicalBWeights.rootWeight_reflection 2) F4RootWeights.rootWeight_reflection
    F4B3.weylHom F4B3.markedSimple F4B3.weylHom_word
    F4B3.parabolicEquiv_length rootWeight_markedSimple w

theorem parabolicEquiv_weightedInversions (w : ClassicalBParabolic.W 2) :
    F4RootWeights.f4WeightedInversions (F4B3.parabolicEquiv w).val =
      ClassicalBWeights.bWeightedInversions 2 w :=
  weylHom_weightedInversions w

local instance : Fintype (ClassicalBParabolic.W 2) := Fintype.ofFinite _
local instance : Fintype
    (rootParabolicSubgroup F4Data.pairing F4Data.base F4ShortOrbit.J) := Fintype.ofFinite _

/-- Transport of the actual sum. Its rank-three value is a separate result. -/
theorem weightedParabolicSubgroupSum_eq_B3 (q : ℕ) :
    (∑ v : rootParabolicSubgroup F4Data.pairing F4Data.base F4ShortOrbit.J,
      q ^ F4RootWeights.f4WeightedInversions v.val) =
      ∑ w : ClassicalBParabolic.W 2, q ^ ClassicalBWeights.bWeightedInversions 2 w := by
  calc
    _ = ∑ w : ClassicalBParabolic.W 2,
        q ^ F4RootWeights.f4WeightedInversions (F4B3.parabolicEquiv w).val :=
      (F4B3.parabolicEquiv.toEquiv.sum_comp
        (fun v => q ^ F4RootWeights.f4WeightedInversions v.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [parabolicEquiv_weightedInversions]

end Atlas.Chevalley.TwistedE6.F4B3WeightTransport
