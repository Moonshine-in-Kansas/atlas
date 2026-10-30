import Atlas.LinearGroups.Chevalley.TwistedE6.WeightedWeylTransport
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBLowerRankParabolic

/-! The intrinsic squared-root-length weights of the actual B root pairing.
The first-coordinate parabolic embedding preserves these weights and the
actual weighted inversion statistic in every rank. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.ClassicalBWeights
open Classical ClassicalData ClassicalBParabolic RootData
  WeightedRootInversions WeightedWeylTransport

/-- Short B roots have weight one, long B roots weight two. -/
def rootWeight (n : ℕ) (β : BRoot (n + 1)) : ℕ :=
  if dot β.val β.val = 1 then 1 else 2

theorem rootWeight_eq_of_scale (n : ℕ) (β : BRoot (n + 1)) :
    rootWeight n β = if corootScale β = 1 then 2 else 1 := by
  unfold rootWeight corootScale
  split_ifs <;> norm_num at *

theorem rootWeight_reflection (n : ℕ) (i : (baseB n).support)
    (β : BRoot (n + 1)) :
    rootWeight n ((pairingB (n + 1)).reflectionPerm i.val β) = rootWeight n β := by
  change (if dot (reflect i.val β.val) (reflect i.val β.val) = 1 then 1 else 2) = _
  rw [reflect_norm]
  rfl

/-- The terminal B simple root is short; the adjacent differences are long. -/
theorem rootWeight_simple (n : ℕ) (i : Fin (n + 1)) :
    rootWeight n (simple n i).val = if i.val < n then 2 else 1 := by
  rw [rootWeight_eq_of_scale]
  change (if corootScale (simpleB n i) = 1 then 2 else 1) = _
  by_cases hi : i.val < n <;> simp [simpleB, hi]

theorem rootWeight_tailSimple (n : ℕ) (i : (baseB n).support) :
    rootWeight (n + 1) (tailSimple n i).val = rootWeight n i.val := by
  rw [tailSimple_val]
  simp only [rootWeight, tailRoot, tailLattice_dot]

/-- Weighted inversions in the actual rank-(n+1) B Weyl image. -/
def bWeightedInversions (n : ℕ) (w : W n) : ℕ :=
  weightedInversions (pairingB (n + 1)) (baseB n) (rootWeight n) w

@[simp] theorem bWeightedInversions_one (n : ℕ) : bWeightedInversions n 1 = 0 :=
  weightedInversions_one (pairingB (n + 1)) (baseB n) (rootWeight n)

/-- The actual tail embedding preserves the statistic, using its proved word
and ordinary-length compatibility and equality of the simple-root weights. -/
theorem tailWeylHom_weightedInversions (n : ℕ) (w : W n) :
    bWeightedInversions (n + 1) (tailWeylHom n w) = bWeightedInversions n w := by
  exact weightedInversions_transport
    (pairingB (n + 1)) (baseB n) (rootWeight n)
    (pairingB (n + 2)) (baseB (n + 1)) (rootWeight (n + 1))
    (rootWeight_reflection n) (rootWeight_reflection (n + 1))
    (tailWeylHom n) (tailSimple n) (tailWeylHom_word n)
    (tailWeylHom_length n) (rootWeight_tailSimple n) w

theorem lowerRankParabolicEquiv_weightedInversions (n : ℕ) (w : W n) :
    bWeightedInversions (n + 1) (lowerRankParabolicEquiv n w).val =
      bWeightedInversions n w :=
  tailWeylHom_weightedInversions n w

end Atlas.Chevalley.TwistedE6.ClassicalBWeights
