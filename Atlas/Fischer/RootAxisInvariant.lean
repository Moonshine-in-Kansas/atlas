import Atlas.Fischer.RootRays
import Atlas.Fischer.OctadicRootMapAxes

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The sum of the actual24 point coordinates. -/
def rootAxisSum (r : Coordinates) : Scalar := ∑ i : Omega, r (.inl i)

theorem rootAxisSum_smul (a : Scalar) (r : Coordinates) :
    rootAxisSum (a • r) = a * rootAxisSum r := by
  simp only [rootAxisSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem rootAxisSum_cube_of_ray_eq (r s : Coordinates) (h : rootRay s = rootRay r) :
    rootAxisSum s ^ 3 = rootAxisSum r ^ 3 := by
  obtain ⟨a, ha, rfl⟩ := (rootRay_eq_iff r s).mp h
  rw [rootAxisSum_smul, mul_pow, ha, one_mul]

theorem rootRay_eq_of_axisSum (r s : Coordinates)
    (hs : rootAxisSum s = rootAxisSum r) (hn : rootAxisSum r ≠ 0)
    (h : rootRay s = rootRay r) : s = r := by
  obtain ⟨a, ha, he⟩ := (rootRay_eq_iff r s).mp h
  have hh : a * rootAxisSum r = 1 * rootAxisSum r := by
    rw [one_mul, ← rootAxisSum_smul, ← he, hs]
  have h1 := mul_right_cancel₀ hn hh
  simpa only [h1, one_smul] using he

theorem rootAxisSum_basic (i : Omega) : rootAxisSum (basicAxis i) = 16 := by
  classical
  simp only [rootAxisSum, basicAxis]
  have h (j : Omega) : (if j = i then (-7 : Scalar) else 1) =
      1 + if j = i then -8 else 0 := by split_ifs <;> norm_num
  simp only [h, Finset.sum_add_distrib]
  simp [Omega, HexIndex]
  norm_num

theorem rootAxisSum_octadic {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    rootAxisSum (octadicRoot Q χ) = 4 := by
  classical
  simp only [rootAxisSum, octadicRoot_axis_coefficient]
  have h (j : Omega) : (if j ∈ O.val then (-1 / 2 : Scalar) else 1 / 2) =
      1 / 2 - if j ∈ O.val then 1 else 0 := by split_ifs <;> norm_num
  simp only [h, Finset.sum_sub_distrib]
  have hc := octad_size O.val O.property
  simp [hc, Omega, HexIndex]
  norm_num

/-- Conditional shape lemma for the actual duadic formula, with the point values
visible as a premise until their independent product calculation is discharged. -/
theorem rootAxisSum_duadic_shape (p : Finset Omega) (hp : p.card = 2) (r : Coordinates)
    (hr : ∀ i, r (.inl i) = if i ∈ p then (-7 / 8 : Scalar) else 1 / 8) :
    rootAxisSum r = 1 := by
  classical
  simp only [rootAxisSum, hr]
  have h (j : Omega) : (if j ∈ p then (-7 / 8 : Scalar) else 1 / 8) =
      1 / 8 - if j ∈ p then 1 else 0 := by split_ifs <;> norm_num
  simp only [h, Finset.sum_sub_distrib]
  simp [hp, Omega, HexIndex]
  norm_num

end Atlas.Fischer
