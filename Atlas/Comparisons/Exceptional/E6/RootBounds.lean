import Atlas.Comparisons.Exceptional.E6.Lattice

/-! Integral coordinate bounds for every norm-one vector. Each bound follows
from positivity after subtracting an explicit multiple of a dual vector. -/
namespace Atlas.Comparisons.E6Lattice

theorem root_bound_0 (x : Fin 6 → ℤ) (hx : norm x = 1) :
    -1 ≤ x 0 ∧ x 0 ≤ 1 := by
  have hp := norm_nonneg (fun j : Fin 6 => 4 * x j - x 0 * (![4,5,6,4,2,3] : Fin 6 → ℤ) j)
  have he : norm (fun j : Fin 6 => 4 * x j - x 0 * (![4,5,6,4,2,3] : Fin 6 → ℤ) j) = 16 * norm x - 6 * x 0^2 := by
    simp [norm]
    ring
  rw [he,hx] at hp
  constructor <;> nlinarith

theorem root_bound_1 (x : Fin 6 → ℤ) (hx : norm x = 1) :
    -2 ≤ x 1 ∧ x 1 ≤ 2 := by
  have hp := norm_nonneg (fun j : Fin 6 => 10 * x j - x 1 * (![5,10,12,8,4,6] : Fin 6 → ℤ) j)
  have he : norm (fun j : Fin 6 => 10 * x j - x 1 * (![5,10,12,8,4,6] : Fin 6 → ℤ) j) = 100 * norm x - 15 * x 1^2 := by
    simp [norm]
    ring
  rw [he,hx] at hp
  constructor <;> nlinarith

theorem root_bound_2 (x : Fin 6 → ℤ) (hx : norm x = 1) :
    -3 ≤ x 2 ∧ x 2 ≤ 3 := by
  have hp := norm_nonneg (fun j : Fin 6 => 18 * x j - x 2 * (![6,12,18,12,6,9] : Fin 6 → ℤ) j)
  have he : norm (fun j : Fin 6 => 18 * x j - x 2 * (![6,12,18,12,6,9] : Fin 6 → ℤ) j) = 324 * norm x - 27 * x 2^2 := by
    simp [norm]
    ring
  rw [he,hx] at hp
  constructor <;> nlinarith

theorem root_bound_3 (x : Fin 6 → ℤ) (hx : norm x = 1) :
    -2 ≤ x 3 ∧ x 3 ≤ 2 := by
  have hp := norm_nonneg (fun j : Fin 6 => 10 * x j - x 3 * (![4,8,12,10,5,6] : Fin 6 → ℤ) j)
  have he : norm (fun j : Fin 6 => 10 * x j - x 3 * (![4,8,12,10,5,6] : Fin 6 → ℤ) j) = 100 * norm x - 15 * x 3^2 := by
    simp [norm]
    ring
  rw [he,hx] at hp
  constructor <;> nlinarith

theorem root_bound_4 (x : Fin 6 → ℤ) (hx : norm x = 1) :
    -1 ≤ x 4 ∧ x 4 ≤ 1 := by
  have hp := norm_nonneg (fun j : Fin 6 => 4 * x j - x 4 * (![2,4,6,5,4,3] : Fin 6 → ℤ) j)
  have he : norm (fun j : Fin 6 => 4 * x j - x 4 * (![2,4,6,5,4,3] : Fin 6 → ℤ) j) = 16 * norm x - 6 * x 4^2 := by
    simp [norm]
    ring
  rw [he,hx] at hp
  constructor <;> nlinarith

theorem root_bound_5 (x : Fin 6 → ℤ) (hx : norm x = 1) :
    -2 ≤ x 5 ∧ x 5 ≤ 2 := by
  have hp := norm_nonneg (fun j : Fin 6 => 6 * x j - x 5 * (![3,6,9,6,3,6] : Fin 6 → ℤ) j)
  have he : norm (fun j : Fin 6 => 6 * x j - x 5 * (![3,6,9,6,3,6] : Fin 6 → ℤ) j) = 36 * norm x - 9 * x 5^2 := by
    simp [norm]
    ring
  rw [he,hx] at hp
  constructor <;> nlinarith

def rootBound : Fin 6 → ℤ := ![1,2,3,2,1,2]

theorem root_coordinate_bounds (x : Fin 6 → ℤ) (hx : norm x = 1) (i : Fin 6) :
    -rootBound i ≤ x i ∧ x i ≤ rootBound i := by
  fin_cases i
  · exact root_bound_0 x hx
  · exact root_bound_1 x hx
  · exact root_bound_2 x hx
  · exact root_bound_3 x hx
  · exact root_bound_4 x hx
  · exact root_bound_5 x hx

end Atlas.Comparisons.E6Lattice
