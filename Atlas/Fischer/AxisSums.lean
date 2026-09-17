import Atlas.Fischer.AxisProductCoefficients
import Atlas.Fischer.ProductMaps

namespace Atlas.Fischer
open Atlas.Codes

noncomputable def axisSum : Coordinates := ∑ i, u i

theorem axisSum_def : axisSum = ∑ i, u i := rfl

theorem basicAxis_eq (i : Omega) : basicAxis i = axisSum - (8 : Scalar) • u i := by
  classical
  funext p
  cases p with
  | inl j =>
    by_cases h : j = i <;> norm_num [basicAxis, axisSum, Finset.sum_apply, h]
  | inr O => simp [basicAxis, axisSum, Finset.sum_apply]

theorem axisBasisProduct_normalForm (i j : Omega) :
    axisBasisProduct i j = (1 / 128 : Scalar) •
      (-axisSum + (16 : Scalar) • u i + (16 : Scalar) • u j +
        if i = j then (16 : Scalar) • axisSum - (128 : Scalar) • u i else 0) := by
  classical
  by_cases h : i = j
  · subst j
    simp only [axisBasisProduct, ite_true]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    change (1 / 128 : Scalar) • ((-81 : Scalar) • u i + (15 : Scalar) • (axisSum - u i)) = _
    congr 1
    module
  · have hf : Finset.univ.filter (fun k : Omega => k ≠ i ∧ k ≠ j) =
        (Finset.univ.erase i).erase j := by
      ext k
      simp [and_comm]
    simp only [axisBasisProduct, if_neg h, hf]
    rw [Finset.sum_erase_eq_sub (by simp [h, Ne.symm h]),
      Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    change (1 / 128 : Scalar) • ((15 : Scalar) • u i + (15 : Scalar) • u j -
      (axisSum - u i - u j)) = _
    congr 1
    module

theorem axisBasisProduct_total (i : Omega) :
    (∑ j, axisBasisProduct i j) = (1 / 16 : Scalar) • axisSum + (2 : Scalar) • u i := by
  classical
  simp only [axisBasisProduct_normalForm, ← Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.sum_const, Finset.card_univ]
  have ho : Fintype.card Omega = 24 := by decide
  simp only [ho, ← Finset.smul_sum, ← axisSum_def]
  module

theorem product_u_axisSum (i : Omega) :
    product (u i) axisSum = (1 / 16 : Scalar) • axisSum + (2 : Scalar) • u i := by
  rw [axisSum, product_sum_right]
  simp only [product_u]
  exact axisBasisProduct_total i

theorem product_axisSum_self : product axisSum axisSum = (7 / 2 : Scalar) • axisSum := by
  rw [axisSum, product_sum_left]
  simp only [← axisSum_def, product_u_axisSum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, ← Finset.smul_sum]
  have ho : Fintype.card Omega = 24 := by decide
  simp only [ho, ← axisSum_def]
  module

end Atlas.Fischer
