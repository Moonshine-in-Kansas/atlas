import Atlas.LinearGroups.Chevalley.Integral.GradedMatrix
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Nilpotent.Defs

/-! UNCHECKED generic continuation: a positive integral support degree makes
an integer matrix nilpotent. No support hypothesis for an actual root model
is supplied here; that remains a separate application obligation. -/
noncomputable section
namespace Atlas.Chevalley.Integral.WeightedSupport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonnegative bound for every absolute coordinate weight. -/
def weightAbsBound (w : ι → ℤ) : ℕ := ∑ i, (w i).natAbs

private theorem weight_bounds (w : ι → ℤ) (i : ι) :
    -(weightAbsBound w : ℤ) ≤ w i ∧ w i ≤ (weightAbsBound w : ℤ) := by
  have hs : (w i).natAbs ≤ weightAbsBound w :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((w j).natAbs)) (Finset.mem_univ i)
  have hc : ((w i).natAbs : ℤ) ≤ (weightAbsBound w : ℤ) := by exact_mod_cast hs
  have hp : w i ≤ ((w i).natAbs : ℤ) := Int.le_natAbs
  have hn : -w i ≤ ((w i).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -w i))
  omega

/-- A concrete uniform exponent: every possible weight difference is at most
2B, whereas a positive integer support degree increases it by more than 2B. -/
theorem pow_eq_zero_of_degree_pos {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι ℤ}
    (hA : Atlas.Chevalley.Integral.WeightedSupport w d A) (hd : 0 < d) :
    A ^ (2 * weightAbsBound w + 1) = 0 := by
  ext i j
  change (A ^ (2 * weightAbsBound w + 1)) i j = 0
  by_contra hij
  have hs := hA.pow (2 * weightAbsBound w + 1) i j hij
  have hi := (weight_bounds w i).2
  have hj := (weight_bounds w j).1
  have hd1 : (1 : ℤ) ≤ d := by omega
  have hb : (0 : ℤ) ≤ (weightAbsBound w : ℤ) := Int.natCast_nonneg _
  have hp : 2 * (weightAbsBound w : ℤ) + 1 ≤
      (2 * (weightAbsBound w : ℤ) + 1) * d := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hd1
        (by omega : (0 : ℤ) ≤ 2 * (weightAbsBound w : ℤ) + 1))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hs
  omega

/-- Positive weight degree implies nilpotence, without a nonempty-index premise. -/
theorem isNilpotent_of_degree_pos {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι ℤ}
    (hA : Atlas.Chevalley.Integral.WeightedSupport w d A) (hd : 0 < d) :
    IsNilpotent A :=
  ⟨2 * weightAbsBound w + 1, hA.pow_eq_zero_of_degree_pos hd⟩

end Atlas.Chevalley.Integral.WeightedSupport
