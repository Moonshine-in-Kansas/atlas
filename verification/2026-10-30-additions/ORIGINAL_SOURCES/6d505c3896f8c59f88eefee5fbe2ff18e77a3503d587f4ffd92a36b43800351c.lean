import FamilyWork.F4B3WeightTransport
import FamilyWork.WeightedB3Sum

/-! Evaluation on the literal marked F4/B3 parabolic, transported from
the actual B3 signed-axis factorization. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.F4B3Weights
open Classical RootData

local instance : Fintype
    (rootParabolicSubgroup F4Data.pairing F4Data.base F4ShortOrbit.J) := Fintype.ofFinite _

theorem weightedParabolicSubgroup_sum (q : ℕ) :
    (∑ v : rootParabolicSubgroup F4Data.pairing F4Data.base F4ShortOrbit.J,
      q ^ F4RootWeights.f4WeightedInversions v.val) =
      (1 + q) * (1 + q ^ 2) * (1 + q ^ 3) * (1 + q ^ 2 + q ^ 4) * (1 + q ^ 5) := by
  rw [F4B3WeightTransport.weightedParabolicSubgroupSum_eq_B3,
    WeightedB3Sum.bWeightedWeylSum_rank3]

end Atlas.Chevalley.TwistedE6.F4B3Weights
