import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing
import Lean.Elab.Tactic.Omega

/-! Matrix depth for an integer coordinate grading. Depth lower bounds
add under multiplication, without dividing by any coefficient. -/

namespace Atlas.Matrix
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Entries below the specified height difference vanish. This is a condition
on a matrix, usually the difference of a unitriangular matrix and the identity. -/
def HeightAtLeast (w : ι → ℤ) (d : ℤ) (A : Matrix ι ι R) : Prop :=
  ∀ row col, w row < w col + d → A row col = 0

namespace HeightAtLeast

theorem add {w : ι → ℤ} {d : ℤ} {A B : Matrix ι ι R}
    (hA : HeightAtLeast w d A) (hB : HeightAtLeast w d B) :
    HeightAtLeast w d (A + B) := by
  intro row col h
  simp only [Matrix.add_apply, hA row col h, hB row col h, add_zero]

theorem mono {w : ι → ℤ} {a b : ℤ} {A : Matrix ι ι R}
    (hA : HeightAtLeast w b A) (hab : a ≤ b) : HeightAtLeast w a A := by
  intro row col h
  apply hA row col
  omega

/-- Matrix multiplication adds depth bounds. -/
theorem mul {w : ι → ℤ} {a b : ℤ} {A B : Matrix ι ι R}
    (hA : HeightAtLeast w a A) (hB : HeightAtLeast w b B) :
    HeightAtLeast w (a + b) (A * B) := by
  intro row col h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hleft : w row < w k + a
  · rw [hA row k hleft, zero_mul]
  · have hright : w k < w col + b := by omega
    rw [hB k col hright, mul_zero]

/-- Products of matrices congruent to one at depth d retain that congruence. -/
theorem mul_sub_one {w : ι → ℤ} {d : ℤ} {A B : Matrix ι ι R}
    (hd : 0 ≤ d) (hA : HeightAtLeast w d (A - 1))
    (hB : HeightAtLeast w d (B - 1)) :
    HeightAtLeast w d (A * B - 1) := by
  have he : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by
    noncomm_ring
  rw [he]
  exact (hA.add hB).add ((hA.mul hB).mono (by omega))

/-- At a positive first depth d the cross term has depth at least 2d, so the
degree-d entries of a product are the sum of the degree-d entries. -/
theorem mul_sub_one_first_degree {w : ι → ℤ} {d : ℤ} {A B : Matrix ι ι R}
    (hd : 0 < d) (hA : HeightAtLeast w d (A - 1))
    (hB : HeightAtLeast w d (B - 1)) (row col : ι)
    (hdegree : w row = w col + d) :
    (A * B - 1) row col = (A - 1) row col + (B - 1) row col := by
  have hz := (hA.mul hB) row col (show w row < w col + (d + d) by omega)
  have he : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by
    noncomm_ring
  rw [he]
  simp only [Matrix.add_apply, hz, add_zero]

end HeightAtLeast

/-- A matrix homogeneous for a transported grading stays homogeneous after
left and right multiplication by matrices transporting the grading back.
The matrices need not be inverses for this support statement. -/
theorem conjugate_eq_zero_of_height_ne
    (w v : ι → ℤ) (d : ℤ) (G A H : Matrix ι ι R)
    (hG : ∀ row col, G row col ≠ 0 → w row = v col)
    (hH : ∀ row col, H row col ≠ 0 → v row = w col)
    (hA : ∀ row col, v row ≠ v col + d → A row col = 0)
    (row col : ι) (hne : w row ≠ w col + d) :
    (G * A * H) row col = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hHzero : H k col = 0
  · rw [hHzero, mul_zero]
  · have hGA : (G * A) row k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hGzero : G row j = 0
      · rw [hGzero, zero_mul]
      · have hdiff : v j ≠ v k + d := by
          intro he
          apply hne
          rw [hG row j hGzero, he, hH k col hHzero]
        rw [hA j k hdiff, mul_zero]
    rw [hGA, zero_mul]

end Atlas.Matrix
