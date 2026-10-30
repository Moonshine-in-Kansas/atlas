import Atlas.LinearGroups.Chevalley.TwistedE6.FixedWeylIdentification
import Atlas.LinearGroups.Chevalley.TwistedE6.WeightedRootInversions

/-! Actual long/short F4 root weights and their weighted inversion sum.
Weight invariance is proved by the integral quadratic form and the existing
coordinate reconstruction, with no root or Weyl enumeration. Source only. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6.F4RootWeights
open Classical RootData F4ActionAdapter FoldedWeylIdentification WeightedRootInversions

/-- Twice the long-root contribution and once the short-root contribution. -/
def rootWeight (β : F4Data.Root) : ℕ :=
  if Atlas.F4.RootData.IsLong β then 2 else 1

theorem rootWeight_pos (β : F4Data.Root) : 0 < rootWeight β := by
  unfold rootWeight
  split_ifs <;> norm_num

/-- The actual F4 norm in the marked simple-root coordinates. -/
def coefficientNorm (x : Fin 4 → ℤ) : ℤ :=
  2 * x 0 ^ 2 + 2 * x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 -
    2 * x 0 * x 1 - 2 * x 1 * x 2 - x 2 * x 3

/-- Doubled Cartesian coordinates in the existing F4 root-label model. -/
def coefficientCartesian (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![x 3, 2 * x 0 - x 3, -2 * x 0 + 2 * x 1 - x 3,
    -2 * x 1 + 2 * x 2 - x 3]

theorem coefficientCartesian_root (β : F4Data.Root) :
    Atlas.F4.RootData.coordinates β = coefficientCartesian (F4Table.coordinates β) := by
  calc
    _ = ∑ i : Fin 4, Atlas.F4.RootData.simpleCoefficients β i •
        Atlas.F4.RootData.coordinates (Atlas.F4.RootData.simpleRoot i) :=
      Atlas.F4.RootData.simpleCoefficients_reconstruct β
    _ = coefficientCartesian (F4Table.coordinates β) := by
      change (∑ i : Fin 4, Atlas.F4.RootData.simpleCoefficients β i •
        Atlas.F4.RootData.coordinates (Atlas.F4.RootData.simpleRoot i)) =
          coefficientCartesian (Atlas.F4.RootData.simpleCoefficients β)
      simp only [Atlas.F4.RootData.simpleRoot_coordinates]
      funext j
      fin_cases j <;>
        simp [coefficientCartesian, Fin.sum_univ_succ, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul] <;> ring

theorem norm_coefficientCartesian (x : Fin 4 → ℤ) :
    Atlas.F4.RootData.normSquared (coefficientCartesian x) = 4 * coefficientNorm x := by
  simp [Atlas.F4.RootData.normSquared, coefficientCartesian, coefficientNorm,
    Fin.sum_univ_succ] <;> ring

/-- The form really measures the existing long/short root partition. -/
theorem coefficientNorm_root (β : F4Data.Root) :
    coefficientNorm (F4Table.coordinates β) = (rootWeight β : ℤ) := by
  have hn := Atlas.F4.RootData.norm_coordinates β
  rw [coefficientCartesian_root, norm_coefficientCartesian] at hn
  by_cases h : Atlas.F4.RootData.IsLong β
  · simp only [if_pos h] at hn
    simp only [rootWeight, if_pos h, Nat.cast_ofNat]
    omega
  · simp only [if_neg h] at hn
    simp only [rootWeight, if_neg h, Nat.cast_ofNat]
    omega

/-- The same four literal formulas preserve this norm over the integral lattice. -/
theorem coefficientNorm_reflection (a : Fin 4) (x : Fin 4 → ℤ) :
    coefficientNorm (foldedReflection ℤ a x) = coefficientNorm x := by
  fin_cases a <;> simp [coefficientNorm, foldedReflection] <;> ring

theorem rootWeight_simple_reflection (a : Fin 4) (β : F4Data.Root) :
    rootWeight ((f4Simple a).val β) = rootWeight β := by
  have he : (rootWeight ((f4Simple a).val β) : ℤ) = (rootWeight β : ℤ) := by
    rw [← coefficientNorm_root, ← coefficientNorm_root, f4Simple_coordinates,
      coefficientNorm_reflection]
  exact_mod_cast he

theorem rootWeight_reflection (i : F4Data.base.support) (β : F4Data.Root) :
    rootWeight (F4Data.pairing.reflectionPerm i.val β) = rootWeight β := by
  obtain ⟨a, rfl⟩ := F4Data.baseIndexEquiv.surjective i
  exact rootWeight_simple_reflection a β

/-- Invariance for the full existing Weyl image follows from actual simple-word generation. -/
theorem rootWeight_weyl (w : F4Weyl) (β : F4Data.Root) :
    rootWeight (w.val β) = rootWeight β := by
  obtain ⟨l, rfl⟩ := exists_f4Word w
  induction l generalizing β with
  | nil => rfl
  | cons a l ih =>
    rw [f4Word_cons]
    change rootWeight ((f4Simple a).val ((f4Word l).val β)) = rootWeight β
    rw [rootWeight_simple_reflection, ih]

/-- Exact markings: long simple nodes 0,1 have weight 2; short nodes 2,3 have weight 1. -/
theorem rootWeight_simple (a : Fin 4) :
    rootWeight (F4Data.baseIndexEquiv a).val = e6FoldedWeylWeight a := by
  have he : (rootWeight (F4Data.baseIndexEquiv a).val : ℤ) =
      (e6FoldedWeylWeight a : ℤ) := by
    rw [← coefficientNorm_root, f4BaseIndex_root, F4Table.simple_coordinates]
    fin_cases a <;> norm_num [coefficientNorm, e6FoldedWeylWeight, Pi.single_apply] <;> decide
  exact_mod_cast he

/-- An independent statistic on actual F4 root inversions, before any E6 comparison. -/
def f4WeightedInversions (w : F4Weyl) : ℕ :=
  weightedInversions F4Data.pairing F4Data.base rootWeight w

theorem f4WeightedInversions_eq_sum (w : F4Weyl) :
    f4WeightedInversions w =
      ∑ β ∈ rootInversions F4Data.pairing F4Data.base w,
        if Atlas.F4.RootData.IsLong β then 2 else 1 := rfl

@[simp] theorem f4WeightedInversions_one : f4WeightedInversions 1 = 0 :=
  weightedInversions_one F4Data.pairing F4Data.base rootWeight

theorem f4WeightedInversions_mul_simple_of_positive (w : F4Weyl) (a : Fin 4)
    (hpos : F4Data.base.IsPos (w.val (F4Data.baseIndexEquiv a).val)) :
    f4WeightedInversions (w * f4Simple a) =
      f4WeightedInversions w + e6FoldedWeylWeight a := by
  simpa only [f4WeightedInversions, f4Simple, rootWeight_simple] using
    weightedInversions_mul_simple_of_positive F4Data.pairing F4Data.base rootWeight
      rootWeight_reflection w (F4Data.baseIndexEquiv a) hpos

theorem f4WeightedInversions_mul_simple_of_negative (w : F4Weyl) (a : Fin 4)
    (hneg : ¬ F4Data.base.IsPos (w.val (F4Data.baseIndexEquiv a).val)) :
    f4WeightedInversions (w * f4Simple a) + e6FoldedWeylWeight a =
      f4WeightedInversions w := by
  simpa only [f4WeightedInversions, f4Simple, rootWeight_simple] using
    weightedInversions_mul_simple_of_negative F4Data.pairing F4Data.base rootWeight
      rootWeight_reflection w (F4Data.baseIndexEquiv a) hneg

theorem f4WeightedInversions_simple (a : Fin 4) :
    f4WeightedInversions (f4Simple a) = e6FoldedWeylWeight a := by
  simpa only [one_mul, f4WeightedInversions_one, zero_add] using
    f4WeightedInversions_mul_simple_of_positive 1 a
      (F4Data.base.isPos_of_mem_support (F4Data.baseIndexEquiv a).property)

end Atlas.Chevalley.TwistedE6.F4RootWeights
