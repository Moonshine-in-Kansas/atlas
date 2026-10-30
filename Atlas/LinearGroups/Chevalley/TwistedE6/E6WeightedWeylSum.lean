import Atlas.LinearGroups.Chevalley.TwistedE6.E6OrderPolynomial
import Atlas.LinearGroups.Chevalley.TwistedE6.F4WeightedCosets
import Atlas.LinearGroups.Chevalley.TwistedE6.F4B3Weights
import Atlas.LinearGroups.Chevalley.TwistedE6.WeightedParabolicFactor

/-! Evaluation of the whole actual F4 weighted Weyl sum by the already proved
actual parabolic factors. No formula is supplied as a theorem hypothesis.
Source only; verification is separate. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.ClosedOrder
open Classical RootData F4ActionAdapter F4RootWeights

local instance : Fintype F4Weyl := Fintype.ofFinite _
local instance : Fintype
    (rootParabolicRepresentatives F4Data.pairing F4Data.base F4ShortOrbit.J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance : Fintype
    (rootParabolicSubgroup F4Data.pairing F4Data.base F4ShortOrbit.J) :=
  Fintype.ofFinite _

/-- The full sum on the actual F4 root-permutation Weyl image, with long-root
weight two and short-root weight one. This holds for every natural q. -/
theorem f4WeightedWeylSum (q : ℕ) :
    (∑ w : F4Weyl, q ^ f4WeightedInversions w) = weightedWeylPolynomial q := by
  have hfactor : (∑ w : F4Weyl, q ^ f4WeightedInversions w) =
      (∑ x : rootParabolicRepresentatives F4Data.pairing F4Data.base F4ShortOrbit.J,
        q ^ f4WeightedInversions x.val) *
      (∑ v : rootParabolicSubgroup F4Data.pairing F4Data.base F4ShortOrbit.J,
        q ^ f4WeightedInversions v.val) := by
    simpa only [f4WeightedInversions] using
      WeightedParabolicFactor.weightedWeylSum_parabolic_factor
        F4Data.pairing F4Data.base rootWeight rootWeight_reflection F4ShortOrbit.J q
  simpa only [F4WeightedCosets.weightedParabolicRepresentatives_sum,
    F4B3Weights.weightedParabolicSubgroup_sum, weightedWeylPolynomial] using hfactor

/-- Expanded product form, retaining the unequal weights rather than ordinary F4 length. -/
theorem f4WeightedWeylSum_product (q : ℕ) :
    (∑ w : F4Weyl, q ^ f4WeightedInversions w) =
      ((1 + q + q ^ 2) * (1 + q ^ 4) * (1 + q ^ 6) * (1 + q ^ 9)) *
        ((1 + q) * (1 + q ^ 2) * (1 + q ^ 3) * (1 + q ^ 2 + q ^ 4) * (1 + q ^ 5)) :=
  f4WeightedWeylSum q

end Atlas.Chevalley.TwistedE6.ClosedOrder
