import FamilyWork.ClassicalBWeights
import FamilyWork.WeightedParabolicFactor
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBParabolicRepresentatives
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Source-only draft: weighted sums for the actual signed-axis representatives
and the actual B Weyl groups in ranks one, two and three.

The root weights and lower-rank transport come from ClassicalBWeights. Reduced
words and weighted parabolic factorization come from the existing actual root
pairings and WeightedParabolicFactor. Only the 2, 4 and 6 short path words are
simplified below; no Weyl-group elements are enumerated. This file has not been
compiled or audited by its author. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6.WeightedB3Sum
open Classical ClassicalData ClassicalBParabolic RootData
  ClassicalBWeights WeightedParabolicFactor

local instance (n : ℕ) : Fintype (W n) := Fintype.ofFinite _
local instance (n : ℕ) :
    Fintype (rootParabolicRepresentatives (pairingB (n + 1)) (baseB n) (J n)) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance (n : ℕ) :
    Fintype (rootParabolicSubgroup (pairingB (n + 1)) (baseB n) (J n)) :=
  Fintype.ofFinite _

/-- Sum of the actual simple-root weights along the existing signed-axis word.
The terminal node n is short, and all preceding nodes are long. -/
def axisWordWeight (n k : ℕ) : ℕ :=
  ((axisPath n k).1.map (fun i => if i.val < n then 2 else 1)).sum

/-- The existing path has exactly as many letters as its proved ordinary length. -/
theorem axisPath_isReduced (n : ℕ) (k : Fin (2 * (n + 1))) :
    IsReducedRootWord (pairingB (n + 1)) (baseB n)
      ((axisPath n k.val).1.map (simple n)) := by
  change rootWeylLength (pairingB (n + 1)) (baseB n) (pathRepresentative n k) =
    ((axisPath n k.val).1.map (simple n)).length
  rw [pathRepresentative_length, List.length_map, axisPath_word_length]

/-- The literal path weight is the actual weighted root-inversion statistic. -/
theorem pathRepresentative_weightedInversions (n : ℕ) (k : Fin (2 * (n + 1))) :
    bWeightedInversions n (pathRepresentative n k) = axisWordWeight n k.val := by
  simpa only [bWeightedInversions, pathRepresentative, axisWordWeight,
    List.map_map, Function.comp_def, rootWeight_simple] using
    (weightedInversions_reduced_word (pairingB (n + 1)) (baseB n) (rootWeight n)
      (rootWeight_reflection n) ((axisPath n k.val).1.map (simple n))
      (axisPath_isReduced n k))

theorem pathRepresentativeEquiv_weightedInversions
    (n : ℕ) (k : Fin (2 * (n + 1))) :
    bWeightedInversions n (pathRepresentativeEquiv n k).val =
      axisWordWeight n k.val :=
  pathRepresentative_weightedInversions n k

/-- The sum over the actual rank-(n+1) B root-permutation Weyl image. -/
def bWeightedWeylSum (n q : ℕ) : ℕ :=
  ∑ w : W n, q ^ bWeightedInversions n w

/-- A sum over the signed-axis path indices, to be identified with actual
minimal right-parabolic representatives by pathRepresentativeEquiv. -/
def signedAxisWeightedSum (n q : ℕ) : ℕ :=
  ∑ k : Fin (2 * (n + 1)), q ^ axisWordWeight n k.val

/-- The two rank-one paths are [] and [0], with node 0 short. -/
theorem axisWordWeight_rank1 (k : Fin 2) :
    axisWordWeight 0 k.val = ![0, 1] k := by
  fin_cases k <;>
    norm_num [axisWordWeight, axisPath, axisForwardIndex, axisStep, Equiv.swap_apply_def]

/-- The rank-two paths are [], [0], [1,0], [0,1,0]; node 1 is short. -/
theorem axisWordWeight_rank2 (k : Fin 4) :
    axisWordWeight 1 k.val = ![0, 2, 3, 5] k := by
  fin_cases k <;>
    norm_num [axisWordWeight, axisPath, axisForwardIndex, axisStep, Equiv.swap_apply_def]

/-- The rank-three paths are [], [0], [1,0], [2,1,0], [1,2,1,0],
[0,1,2,1,0]; node 2 is short. -/
theorem axisWordWeight_rank3 (k : Fin 6) :
    axisWordWeight 2 k.val = ![0, 2, 4, 5, 7, 9] k := by
  fin_cases k <;>
    norm_num [axisWordWeight, axisPath, axisForwardIndex, axisStep, Equiv.swap_apply_def]

theorem signedAxisWeightedSum_rank1 (q : ℕ) :
    signedAxisWeightedSum 0 q = 1 + q := by
  change (∑ k : Fin 2, q ^ axisWordWeight 0 k.val) = _
  simp_rw [axisWordWeight_rank1]
  norm_num [Fin.sum_univ_succ]

theorem signedAxisWeightedSum_rank2 (q : ℕ) :
    signedAxisWeightedSum 1 q = (1 + q ^ 2) * (1 + q ^ 3) := by
  change (∑ k : Fin 4, q ^ axisWordWeight 1 k.val) = _
  simp_rw [axisWordWeight_rank2]
  norm_num [Fin.sum_univ_succ] <;> ring

theorem signedAxisWeightedSum_rank3 (q : ℕ) :
    signedAxisWeightedSum 2 q = (1 + q ^ 2 + q ^ 4) * (1 + q ^ 5) := by
  change (∑ k : Fin 6, q ^ axisWordWeight 2 k.val) = _
  simp_rw [axisWordWeight_rank3]
  norm_num [Fin.sum_univ_succ] <;> ring

/-- The finite path sum is the sum over actual minimal representatives. -/
theorem parabolicRepresentatives_weightedSum (n q : ℕ) :
    (∑ x : rootParabolicRepresentatives (pairingB (n + 1)) (baseB n) (J n),
      q ^ bWeightedInversions n x.val) = signedAxisWeightedSum n q := by
  rw [← (pathRepresentativeEquiv n).sum_comp
    (fun x => q ^ bWeightedInversions n x.val)]
  simp only [pathRepresentativeEquiv_weightedInversions, signedAxisWeightedSum]

/-- The actual first-node parabolic has the intrinsic lower-rank weighted sum. -/
theorem lowerRankParabolic_weightedSum (n q : ℕ) :
    (∑ v : rootParabolicSubgroup (pairingB (n + 2)) (baseB (n + 1)) (J (n + 1)),
      q ^ bWeightedInversions (n + 1) v.val) = bWeightedWeylSum n q := by
  rw [← (lowerRankParabolicEquiv n).toEquiv.sum_comp
    (fun v => q ^ bWeightedInversions (n + 1) v.val)]
  change (∑ w : W n,
    q ^ bWeightedInversions (n + 1) (lowerRankParabolicEquiv n w).val) = _
  simp only [lowerRankParabolicEquiv_weightedInversions, bWeightedWeylSum]

/-- The recurrence uses the actual parabolic product equivalence and the
proved weighted transport. No numerical Weyl-sum identity is a hypothesis. -/
theorem bWeightedWeylSum_succ (n q : ℕ) :
    bWeightedWeylSum (n + 1) q =
      signedAxisWeightedSum (n + 1) q * bWeightedWeylSum n q := by
  have h := weightedWeylSum_parabolic_factor
    (pairingB (n + 2)) (baseB (n + 1)) (rootWeight (n + 1))
    (rootWeight_reflection (n + 1)) (J (n + 1)) q
  change bWeightedWeylSum (n + 1) q =
    (∑ x : rootParabolicRepresentatives (pairingB (n + 2)) (baseB (n + 1))
      (J (n + 1)), q ^ bWeightedInversions (n + 1) x.val) *
    (∑ v : rootParabolicSubgroup (pairingB (n + 2)) (baseB (n + 1))
      (J (n + 1)), q ^ bWeightedInversions (n + 1) v.val) at h
  rw [parabolicRepresentatives_weightedSum, lowerRankParabolic_weightedSum] at h
  exact h

private theorem J_zero : J 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨k, rfl⟩ := (baseBIndexEquiv 0).surjective i
  have hk : k = 0 := by
    apply Fin.ext
    have hklt := k.isLt
    change k.val = 0
    omega
  subst k
  exact (Finset.mem_erase.mp hi).1 rfl

private theorem rankOne_parabolic_eq_one
    (v : rootParabolicSubgroup (pairingB 1) (baseB 0) (J 0)) : v.val = 1 := by
  have hbot : rootParabolicSubgroup (pairingB 1) (baseB 0) (J 0) = ⊥ := by
    simp [rootParabolicSubgroup, J_zero]
  exact Subgroup.mem_bot.mp (hbot ▸ v.property)

private theorem rankOne_parabolic_weightedSum (q : ℕ) :
    (∑ v : rootParabolicSubgroup (pairingB 1) (baseB 0) (J 0),
      q ^ bWeightedInversions 0 v.val) = 1 := by
  letI : Unique (rootParabolicSubgroup (pairingB 1) (baseB 0) (J 0)) := {
    default := 1
    uniq := fun v => Subtype.ext (rankOne_parabolic_eq_one v) }
  simp only [rankOne_parabolic_eq_one, bWeightedInversions_one, pow_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]

/-- Rank one is obtained from the actual two paths and trivial parabolic. -/
theorem bWeightedWeylSum_rank1 (q : ℕ) :
    bWeightedWeylSum 0 q = 1 + q := by
  have h := weightedWeylSum_parabolic_factor (pairingB 1) (baseB 0) (rootWeight 0)
    (rootWeight_reflection 0) (J 0) q
  change bWeightedWeylSum 0 q =
    (∑ x : rootParabolicRepresentatives (pairingB 1) (baseB 0) (J 0),
      q ^ bWeightedInversions 0 x.val) *
    (∑ v : rootParabolicSubgroup (pairingB 1) (baseB 0) (J 0),
      q ^ bWeightedInversions 0 v.val) at h
  rw [parabolicRepresentatives_weightedSum, rankOne_parabolic_weightedSum,
    mul_one, signedAxisWeightedSum_rank1] at h
  exact h

theorem bWeightedWeylSum_rank2 (q : ℕ) :
    bWeightedWeylSum 1 q = (1 + q) * (1 + q ^ 2) * (1 + q ^ 3) := by
  rw [bWeightedWeylSum_succ 0 q, signedAxisWeightedSum_rank2,
    bWeightedWeylSum_rank1]
  ring

/-- The weighted sum over the actual B3 root-permutation Weyl group, with
long-root weight two and short-root weight one, for every natural q. -/
theorem bWeightedWeylSum_rank3 (q : ℕ) :
    (∑ w : W 2, q ^ bWeightedInversions 2 w) =
      (1 + q) * (1 + q ^ 2) * (1 + q ^ 3) * (1 + q ^ 2 + q ^ 4) * (1 + q ^ 5) := by
  change bWeightedWeylSum 2 q = _
  rw [bWeightedWeylSum_succ 1 q, signedAxisWeightedSum_rank3,
    bWeightedWeylSum_rank2]
  ring

end Atlas.Chevalley.TwistedE6.WeightedB3Sum
