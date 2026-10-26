import Atlas.LinearAlgebra.HeightUnitriangular

/-! Transport of the complete matrix height filtration under conjugation.
The support conditions apply to every matrix entry, including equal-height blocks. -/

namespace Atlas.Matrix.HeightUnitriangular

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Conjugation transports unitriangularity when the conjugating matrices carry
the complete old height grading to the complete new height grading. -/
theorem conj_of_height_transport {v w : ι → ℤ} {A g h : Matrix ι ι R}
    (hA : Atlas.Matrix.HeightUnitriangular v A)
    (hg : ∀ row col, g row col ≠ 0 → w row = v col)
    (hh : ∀ row col, h row col ≠ 0 → v row = w col)
    (hinv : g * h = 1) :
    Atlas.Matrix.HeightUnitriangular w (g * A * h) := by
  intro row col hrowcol
  have hterm (k l : ι) :
      g row k * A k l * h l col =
        g row k * (1 : Matrix ι ι R) k l * h l col := by
    by_cases hg0 : g row k = 0
    · simp only [hg0, zero_mul]
    by_cases hh0 : h l col = 0
    · simp only [hh0, mul_zero]
    have hkl : v k ≤ v l := by
      rw [← hg row k hg0, hh l col hh0]
      exact hrowcol
    rw [hA k l hkl]
  calc
    (g * A * h) row col = (g * (1 : Matrix ι ι R) * h) row col := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ =>
        Finset.sum_congr rfl (fun k _ => hterm k l))
    _ = (1 : Matrix ι ι R) row col := by rw [Matrix.mul_one, hinv]

end Atlas.Matrix.HeightUnitriangular
