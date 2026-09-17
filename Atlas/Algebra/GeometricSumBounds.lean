import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Atlas.Arithmetic

def geometricSum (q m : ℕ) : ℕ := ∑ i ∈ Finset.range m,q^i

theorem geometricSum_succ (q m : ℕ) :
    geometricSum q (m+1) = geometricSum q m + q^m := Finset.sum_range_succ _ _

theorem geometricSum_shift (q m : ℕ) :
    geometricSum q (m+1) = q*geometricSum q m+1 := by
  unfold geometricSum
  rw [Finset.sum_range_succ']
  simp only [pow_succ,pow_zero,← Finset.sum_mul]
  ring

theorem geometricSum_lt_power {q : ℕ} (hq : 2 ≤ q) (m : ℕ) :
    geometricSum q m < q^m := by
  induction m with
  | zero => simp [geometricSum]
  | succ m ih =>
    rw [geometricSum_succ,pow_succ]
    have h := Nat.mul_le_mul_left (q^m) hq
    omega

theorem geometricSum_gt_one {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) :
    1 < geometricSum q m := by
  have h : geometricSum q 2 ≤ geometricSum q m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm) (fun _ _ _ => Nat.zero_le _)
  have h2 : geometricSum q 2=1+q := by simp [geometricSum,Finset.sum_range_succ]
  rw [h2] at h
  omega

/-- The two proper nonsingleton block sizes in a symplectic rank-three action
cannot divide the whole geometric point count. -/
theorem geometric_block_nondivisibility {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) :
    ¬ geometricSum q m ∣ geometricSum q (m+1) ∧
      ¬ (1+q^m) ∣ geometricSum q (m+1) := by
  have hA := geometricSum_gt_one hq hm
  have hAt := geometricSum_lt_power hq m
  constructor
  · intro hd
    rw [geometricSum_shift] at hd
    have h1 : geometricSum q m ∣ 1 :=
      (Nat.dvd_add_iff_right (dvd_mul_left (geometricSum q m) q)).mpr hd
    have := Nat.le_of_dvd (by decide : 0 < 1) h1
    omega
  · rintro ⟨k,hk⟩
    rw [geometricSum_succ] at hk
    by_cases hle : k ≤ 1
    · have := Nat.mul_le_mul_left (1+q^m) hle
      nlinarith
    · have := Nat.mul_le_mul_left (1+q^m) (show 2 ≤ k by omega)
      nlinarith

end Atlas.Arithmetic
