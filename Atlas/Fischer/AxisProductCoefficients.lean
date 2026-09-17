import Atlas.Fischer.CoordinateEvaluation

namespace Atlas.Fischer
open Atlas.Codes

theorem axisBasisProduct_axis_apply (i j k : Omega) :
    axisBasisProduct i j (Sum.inl k) =
      if i = j then (if k = i then (-81 / 128 : Scalar) else 15 / 128)
      else if k = i ∨ k = j then 15 / 128 else -1 / 128 := by
  classical
  by_cases hij : i = j
  · subst j
    by_cases hki : k = i <;>
      norm_num [axisBasisProduct, Finset.sum_apply, hki, Pi.smul_apply, smul_eq_mul]
  · by_cases hki : k = i <;> by_cases hkj : k = j <;>
      norm_num [axisBasisProduct, Finset.sum_apply, hij, Ne.symm hij, hki, hkj, Pi.smul_apply, smul_eq_mul]

@[simp] theorem axisBasisProduct_octad_apply (i j : Omega) (O : Octad) :
    axisBasisProduct i j (Sum.inr O) = 0 := by
  classical
  unfold axisBasisProduct
  split_ifs <;> simp [Finset.sum_apply]

@[simp] theorem axisOctadBasisProduct_axis_apply (i j : Omega) (O : Octad) :
    axisOctadBasisProduct i O (Sum.inl j) = 0 := by
  classical
  simp [axisOctadBasisProduct]

theorem axisOctadBasisProduct_octad_apply (i : Omega) (O P : Octad) :
    axisOctadBasisProduct i O (Sum.inr P) =
      if P = O then (if i ∈ O.val then (3 / 16 : Scalar) else -1 / 16) else 0 := by
  classical
  by_cases h : P = O <;> simp [axisOctadBasisProduct, h]

theorem octadBasisProduct_axis_apply (O P : Octad) (i : Omega) :
    octadBasisProduct O P (Sum.inl i) =
      if O = P then (if i ∈ O.val then (3 / 2 : Scalar) else -1 / 2) else 0 := by
  classical
  by_cases h : O = P
  · subst P
    simp only [octadBasisProduct, ite_true]
    by_cases hi : i ∈ O.val <;>
      norm_num [Finset.sum_apply, hi, Pi.smul_apply, smul_eq_mul]
  · unfold octadBasisProduct
    rw [if_neg h]
    split_ifs <;> simp [h]

theorem axisBasisProduct_cubic_switch (i j k : Omega) :
    axisBasisProduct j k (Sum.inl i) = axisBasisProduct i k (Sum.inl j) := by
  classical
  rw [axisBasisProduct_axis_apply, axisBasisProduct_axis_apply]
  by_cases hij : i = j
  · subst j; rfl
  · by_cases hik : i = k
    · subst k; simp [hij, Ne.symm hij]
    · by_cases hjk : j = k
      · subst k; simp [hij, Ne.symm hij]
      · simp [hij, Ne.symm hij, hik, hjk]

end Atlas.Fischer
