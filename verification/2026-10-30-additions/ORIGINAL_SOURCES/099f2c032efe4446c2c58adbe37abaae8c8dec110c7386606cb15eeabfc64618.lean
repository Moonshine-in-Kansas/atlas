import FamilyWork.F4RootWeights
import FamilyWork.WeightedParabolicFactor
import Atlas.LinearGroups.Chevalley.RootData.F4ParabolicRepresentatives
import Mathlib.Algebra.BigOperators.Fin

/-!
Source-only continuation: the weighted sum on the existing 24 minimal right
coset representatives of the marked F4/B3 parabolic. The simple weights are
the audited actual root weights 2,2,1,1. Only 24 short-root paths are certified;
there is no enumeration of the Weyl group and no ordinary Poincare substitution.
-/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.F4WeightedCosets
open Classical RootData F4Data F4ShortOrbit F4RootWeights
  WeightedRootInversions WeightedParabolicFactor

local instance : Fintype (rootParabolicRepresentatives pairing base J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _

/-- Explicit shortest paths in the existing 24-point short-root orbit.
The first letter acts last on the seed, as in `rootWeylWord` and `word`.
The table is indexed by the existing labels, not by sorted weight. -/
def seedWord : Fin 24 → List (Fin 4) :=
  ![[],
    [3,2,1,2,0,1,3,2,1,0,3,2,1,2,3],
    [3,2,1,2,3],
    [0,1,2,1,0,3,2,1,2,3],
    [0,3,2,1,2,3],
    [1,2,1,0,3,2,1,2,3],
    [1,0,3,2,1,2,3],
    [2,1,0,3,2,1,2,3],
    [3],
    [2,3],
    [1,2,3],
    [2,1,2,3],
    [0,1,2,3],
    [0,2,1,2,3],
    [1,0,2,1,2,3],
    [2,1,0,2,1,2,3],
    [3,2,1,0,2,1,2,3],
    [3,2,1,0,3,2,1,2,3],
    [1,3,2,1,0,3,2,1,2,3],
    [2,1,3,2,1,0,3,2,1,2,3],
    [0,1,3,2,1,0,3,2,1,2,3],
    [2,0,1,3,2,1,0,3,2,1,2,3],
    [1,2,0,1,3,2,1,0,3,2,1,2,3],
    [2,1,2,0,1,3,2,1,0,3,2,1,2,3]]

/-- The actual weights of these paths, in the same short-root label order. -/
def weightedDistance : Fin 24 → ℕ :=
  ![0,21,6,15,8,13,10,11,1,2,4,5,6,7,9,10,11,12,14,15,16,17,19,20]

/-- A bounded certificate against the already established unweighted distance. -/
theorem seedWord_length : ∀ c : Fin 24, (seedWord c).length = distance c := by
  decide +kernel

/-- This checks only the displayed paths in the existing four-by-24 step table. -/
theorem seedWord_seed : ∀ c : Fin 24, (seedWord c).foldr step 0 = c := by
  decide +kernel

theorem seedWord_weight : ∀ c : Fin 24,
    ((seedWord c).map e6FoldedWeylWeight).sum = weightedDistance c := by
  decide +kernel

/-- Reindex the finite path into the actual F4 simple support. -/
def markedSeedWord (c : Fin 24) : List base.support :=
  (seedWord c).map baseIndexEquiv

theorem word_map_baseIndex (l : List (Fin 4)) (c : Fin 24) :
    word (l.map baseIndexEquiv) c = l.foldr step c := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, word, Equiv.symm_apply_apply, List.foldr_cons, ih]

theorem markedSeedWord_length (c : Fin 24) :
    (markedSeedWord c).length = distance c := by
  simpa only [markedSeedWord, List.length_map] using seedWord_length c

theorem markedSeedWord_seed (c : Fin 24) :
    (rootWeylWord pairing base (markedSeedWord c)).val seed = label c := by
  rw [rootWeylWord_val]
  change simpleReflectionWord pairing base (markedSeedWord c) (label 0) = label c
  rw [word_label]
  change label (word ((seedWord c).map baseIndexEquiv) 0) = label c
  rw [word_map_baseIndex, seedWord_seed]

/-- Reducedness follows from the inherited seed-distance lower bound. -/
theorem markedSeedWord_reduced (c : Fin 24) :
    IsReducedRootWord pairing base (markedSeedWord c) := by
  change rootWeylLength pairing base (rootWeylWord pairing base (markedSeedWord c)) =
    (markedSeedWord c).length
  apply Nat.le_antisymm (rootWeylWord_length_le pairing base (markedSeedWord c))
  rw [markedSeedWord_length]
  exact distance_le_rootWeylLength _ c (markedSeedWord_seed c)

/-- The explicit words give the existing representatives, despite the original
definition choosing a shortest word noncomputably. The proof uses the literal
seed stabilizer and actual parabolic length additivity. -/
theorem rootWeylWord_markedSeedWord (c : Fin 24) :
    rootWeylWord pairing base (markedSeedWord c) = (representativeEquiv c).val := by
  change rootWeylWord pairing base (markedSeedWord c) = representative c
  have hfix : ((representative c)⁻¹ *
      rootWeylWord pairing base (markedSeedWord c)).val seed = seed := by
    change (representative c).val.symm
      ((rootWeylWord pairing base (markedSeedWord c)).val seed) = seed
    rw [markedSeedWord_seed, ← representative_seed]
    exact (representative c).val.symm_apply_apply seed
  have hv := (fixes_seed_iff_parabolic _).mp hfix
  have hlen := rootWeylLength_mul_parabolic_of_simple_positive pairing base J
    (representative c) (representative_minimal c)
    ((representative c)⁻¹ * rootWeylWord pairing base (markedSeedWord c)) hv
  have hwlen : rootWeylLength pairing base
      (rootWeylWord pairing base (markedSeedWord c)) = distance c :=
    (markedSeedWord_reduced c).trans (markedSeedWord_length c)
  rw [mul_inv_cancel_left, hwlen, representative_length] at hlen
  have hz : rootWeylLength pairing base
      ((representative c)⁻¹ * rootWeylWord pairing base (markedSeedWord c)) = 0 := by
    omega
  have he := (rootWeylLength_eq_zero_iff pairing base _).mp hz
  exact (inv_mul_eq_one.mp he).symm

/-- The simple-root weights in this word are the actual audited long/short weights. -/
theorem markedSeedWord_weight (c : Fin 24) :
    ((markedSeedWord c).map (fun i => rootWeight i.val)).sum = weightedDistance c := by
  simpa only [markedSeedWord, List.map_map, Function.comp_def, rootWeight_simple] using
    seedWord_weight c

/-- Exact weighted inversion statistic of each existing minimal representative. -/
theorem representativeEquiv_weightedInversions (c : Fin 24) :
    f4WeightedInversions (representativeEquiv c).val = weightedDistance c := by
  change weightedInversions pairing base rootWeight (representativeEquiv c).val = _
  rw [← rootWeylWord_markedSeedWord]
  exact (weightedInversions_reduced_word pairing base rootWeight rootWeight_reflection
    (markedSeedWord c) (markedSeedWord_reduced c)).trans (markedSeedWord_weight c)

/-- Arithmetic identity for the 24 certified weights; the factor orientation is
computed from nodes 0,1 of weight two and nodes 2,3 of weight one. -/
theorem weightedDistance_sum (q : ℕ) :
    (∑ c : Fin 24, q ^ weightedDistance c) =
      (1 + q + q ^ 2) * (1 + q ^ 4) * (1 + q ^ 6) * (1 + q ^ 9) := by
  simp only [weightedDistance, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, pow_zero, add_zero]
  ring

/-- The quotient factor for the literal marked F4/B3 right-parabolic carrier.
The full Weyl sum and the B3 factor are outside this bounded result. -/
theorem weightedParabolicRepresentatives_sum (q : ℕ) :
    (∑ x : rootParabolicRepresentatives pairing base J,
      q ^ f4WeightedInversions x.val) =
      (1 + q + q ^ 2) * (1 + q ^ 4) * (1 + q ^ 6) * (1 + q ^ 9) := by
  calc
    _ = ∑ c : Fin 24, q ^ f4WeightedInversions (representativeEquiv c).val :=
      (representativeEquiv.sum_comp
        (fun x => q ^ f4WeightedInversions x.val)).symm
    _ = ∑ c : Fin 24, q ^ weightedDistance c := by
      apply Finset.sum_congr rfl
      intro c hc
      exact congrArg (fun n : ℕ => q ^ n) (representativeEquiv_weightedInversions c)
    _ = _ := weightedDistance_sum q

end Atlas.Chevalley.TwistedE6.F4WeightedCosets
